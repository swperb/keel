#!/usr/bin/env python3
"""Score agent solutions against hidden tests.

Layout:  evals/results/<run>/<model>/<mode>/<task>.{kl,rs}
         evals/results/<run>/<model>/<mode>/report.json   (agent's own notes)
         evals/results/<run>/tasks.json                    (optional: task dirs in this run)

Modes:   keel        Keel, the agent writes its own contracts (free spec)
         keel-given  Keel, the agent fills in bodies under our spec.kl contracts
         rust        Rust

Usage:   python3 evals/score.py <run-dir>      score a run
         python3 evals/score.py --ref          validate the harness with the reference solutions

Set KEEL_BIN to score with a specific keel binary (default: target/release/keel).

For each solution we record:
  self_ok   the agent's own toolchain accepted it (keel check / rustc)
  outcome   pass | wrong | crash | unverified | harness_reject | compile_fail
            | contract_altered | missing
  silent    self_ok but the hidden tests did not pass: the dangerous case,
            where the agent had every reason to believe it was done
  proved    obligations the Keel verifier proved (machine-checked facts)

In keel-given mode the types, spec fns and function headers (signature,
requires, ensures, decreases) of the task's spec.kl must appear unchanged in
the solution, up to whitespace and comments. Otherwise the outcome is
contract_altered, whatever the tests say (the test result is kept in
test_outcome).
"""
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
KEEL = Path(os.environ.get("KEEL_BIN", ROOT.parent / "target" / "release" / "keel"))
TASKS = sorted(p for p in (ROOT / "tasks").iterdir() if p.is_dir())
EXT = {"keel": "kl", "keel-given": "kl", "rust": "rs"}
SPEC_WORDS = ("requires", "ensures", "invariant", "decreases", "assert", "spec fn", "lemma")


def run(cmd, timeout=120, stdin=None):
    try:
        p = subprocess.run([str(c) for c in cmd], capture_output=True, text=True, timeout=timeout, input=stdin)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return 124, "", "timeout"


# --- Keel item splitter (for the given-spec contract check) -----------------

TOKEN = re.compile(r"\s*(//[^\n]*|[A-Za-z_][A-Za-z0-9_]*|\d[\d_]*|==>|==|!=|<=|>=|&&|\|\||->|\.\.|[^\sA-Za-z0-9_])")
ITEM_KINDS = ("struct", "enum", "spec", "lemma", "fn", "io")


def tokens(src):
    out = []
    pos = 0
    while pos < len(src):
        m = TOKEN.match(src, pos)
        if not m:
            break
        pos = m.end()
        tok = m.group(1)
        if not tok.startswith("//"):
            out.append((tok, m.start(1), m.end(1)))
    return out


def is_literal_brace(toks, j):
    """`Point { x: ...` or `Shape.Circle { r: ...` in a specification."""
    return toks[j - 1][0][:1].isupper() and j + 2 < len(toks) and toks[j + 2][0] == ":"


def keel_items(src):
    """Split a Keel file into top-level items.

    Each item: kind ('struct', 'enum', 'spec fn', 'lemma', 'fn', 'io fn'),
    name, header (normalized text up to the body brace), full (normalized
    text of the whole item), header_src / full_src (original text)."""
    toks = tokens(src)
    items = []
    i = 0
    while i < len(toks):
        t = toks[i][0]
        if t not in ITEM_KINDS:
            i += 1
            continue
        start = i
        if t in ("spec", "io"):
            kind = t + " fn"
            i += 2
        else:
            kind = t
            i += 1
        name = toks[i][0] if i < len(toks) else ""
        # Find the brace that opens the body (for struct/enum: the definition).
        depth = 0
        pending = 0
        body = None
        j = i
        while j < len(toks):
            tok = toks[j][0]
            if depth == 0 and kind not in ("struct", "enum"):
                if tok in ("forall", "exists", "if", "else"):
                    pending += 1
                elif tok == "{" and (pending > 0 or is_literal_brace(toks, j)):
                    pending = max(0, pending - 1)
                    depth += 1
                    j += 1
                    continue
            if tok == "{":
                if depth == 0 and body is None:
                    body = j
                depth += 1
            elif tok == "}":
                depth -= 1
                if depth == 0 and body is not None:
                    break
            j += 1
        if body is None:
            body = j
        end = min(j, len(toks) - 1)
        header = " ".join(x[0] for x in toks[start:body])
        full = " ".join(x[0] for x in toks[start:end + 1])
        items.append({
            "kind": kind,
            "name": name,
            "header": header,
            "full": full,
            "header_src": src[toks[start][1]:toks[body - 1][2]] if body > start else "",
            "full_src": src[toks[start][1]:toks[end][2]],
        })
        i = end + 1
    return items


def contract_diffs(spec_src, sol_src):
    """Items of spec.kl whose contract is missing or changed in the solution."""
    have = {(it["kind"], it["name"]): it for it in keel_items(sol_src)}
    bad = []
    for it in keel_items(spec_src):
        got = have.get((it["kind"], it["name"]))
        key = "header" if it["kind"] in ("fn", "io fn") else "full"
        if got is None or got[key] != it[key]:
            bad.append(f"{it['kind']} {it['name']}")
    return bad


# --- scoring ------------------------------------------------------------------

def run_tests(binary, task):
    code, out, _ = run([binary], timeout=60)
    want = (task / "expected.txt").read_text().split()
    if code != 0:
        return "crash"
    return "pass" if out.split() == want else "wrong"


def score_keel(sol, task, work, given=False):
    src = sol.read_text()
    r = {"contract_lines": sum(1 for l in src.splitlines() if l.strip().startswith(SPEC_WORDS))}
    code, out, _ = run([KEEL, "check", sol, "--json"])
    try:
        j = json.loads(out)
    except json.JSONDecodeError:
        j = {"ok": False, "proved": 0, "diagnostics": []}
    r["self_ok"] = bool(j["ok"])
    r["proved"] = j["proved"] if j["ok"] else 0
    r["self_codes"] = sorted({d["code"] for d in j["diagnostics"]})
    combined = work / "t.kl"
    combined.write_text(src + "\n" + (task / "test.kl").read_text())
    code, out, _ = run([KEEL, "build", combined, "-o", work / "t", "--json"])
    if code != 0:
        try:
            codes = sorted({d["code"] for d in json.loads(out)["diagnostics"]})
        except (json.JSONDecodeError, KeyError):
            codes = ["?"]
        r["outcome"] = "harness_reject" if r["self_ok"] else "unverified"
        r["harness_codes"] = codes
    else:
        r["outcome"] = run_tests(work / "t", task)
    if given:
        r["altered"] = contract_diffs((task / "spec.kl").read_text(), src)
        if r["altered"]:
            r["test_outcome"] = r["outcome"]
            r["outcome"] = "contract_altered"
    return r


def score_rust(sol, task, work):
    src = sol.read_text()
    r = {"proved": 0, "contract_lines": sum(1 for l in src.splitlines() if "assert" in l)}
    code, _, err = run(["rustc", "--edition", "2021", "--crate-type", "lib", "-o", work / "lib.rlib", sol])
    r["self_ok"] = code == 0
    combined = work / "t.rs"
    combined.write_text(src + "\n" + (task / "test.rs").read_text())
    # Debug assertions on: overflow panics instead of silently wrapping.
    code, _, err = run(["rustc", "--edition", "2021", "-C", "opt-level=2", "-C", "debug-assertions=on", "-A", "warnings", "-o", work / "t", combined])
    if code != 0:
        r["outcome"] = "compile_fail"
        return r
    r["outcome"] = run_tests(work / "t", task)
    return r


def mode_tasks(tasks, mode):
    return [t for t in tasks if mode != "keel-given" or (t / "spec.kl").exists()]


def score_dir(d, mode, tasks):
    rows = {}
    report = {}
    if (d / "report.json").exists():
        try:
            report = json.loads((d / "report.json").read_text())
        except json.JSONDecodeError:
            pass
    for task in mode_tasks(tasks, mode):
        sol = d / f"{task.name}.{EXT[mode]}"
        if not sol.exists():
            rows[task.name] = {"outcome": "missing", "self_ok": False, "proved": 0, "contract_lines": 0}
            continue
        with tempfile.TemporaryDirectory() as w:
            if mode == "rust":
                rows[task.name] = score_rust(sol, task, Path(w))
            else:
                rows[task.name] = score_keel(sol, task, Path(w), given=mode == "keel-given")
        rows[task.name]["iterations"] = report.get(task.name, {}).get("iterations")
        rows[task.name]["agent_confident"] = report.get(task.name, {}).get("confident")
    return rows


def summarize(results, usage=None):
    usage = usage or {}
    lines = ["| model | mode | pass | silent failures | not done | contract altered | proved obligations | spec lines | avg toolchain runs | agent tokens | agent seconds |", "|---|---|---|---|---|---|---|---|---|---|---|"]
    for (model, mode), rows in sorted(results.items()):
        n = len(rows)
        passed = sum(r["outcome"] == "pass" for r in rows.values())
        silent = sum(r["self_ok"] and r["outcome"] not in ("pass", "contract_altered") for r in rows.values())
        notdone = sum(not r["self_ok"] for r in rows.values())
        altered = sum(r["outcome"] == "contract_altered" for r in rows.values()) if mode == "keel-given" else "-"
        proved = sum(r["proved"] for r in rows.values())
        spec = sum(r["contract_lines"] for r in rows.values())
        its = [r.get("iterations") for r in rows.values() if isinstance(r.get("iterations"), (int, float))]
        avg = f"{sum(its) / len(its):.1f}" if its else "-"
        u = usage.get(f"{model}/{mode}", {})
        lines.append(f"| {model} | {mode} | {passed}/{n} | {silent} | {notdone} | {altered} | {proved} | {spec} | {avg} | {u.get('tokens', '-')} | {u.get('seconds', '-')} |")
    lines.append("")
    lines.append("| model | mode | task | self_ok | outcome | proved | detail |")
    lines.append("|---|---|---|---|---|---|---|")
    for (model, mode), rows in sorted(results.items()):
        for t, r in rows.items():
            detail = ",".join(r.get("altered", []) or r.get("harness_codes", []) or r.get("self_codes", []))
            if r.get("test_outcome"):
                detail += f" (tests: {r['test_outcome']})"
            lines.append(f"| {model} | {mode} | {t} | {r['self_ok']} | {r['outcome']} | {r['proved']} | {detail} |")
    return "\n".join(lines)


def main():
    if len(sys.argv) == 2 and sys.argv[1] == "--ref":
        with tempfile.TemporaryDirectory() as tmp:
            results = {}
            for mode in EXT:
                d = Path(tmp) / mode
                d.mkdir()
                for task in mode_tasks(TASKS, mode):
                    (d / f"{task.name}.{EXT[mode]}").write_text((task / f"ref.{EXT[mode]}").read_text())
                results[("reference", mode)] = score_dir(d, mode, TASKS)
        print(summarize(results))
        ok = all(r["outcome"] == "pass" for rows in results.values() for r in rows.values())
        sys.exit(0 if ok else 1)
    if len(sys.argv) != 2:
        print(__doc__)
        sys.exit(2)
    run_dir = Path(sys.argv[1])
    tasks = TASKS
    if (run_dir / "tasks.json").exists():
        names = set(json.loads((run_dir / "tasks.json").read_text()))
        tasks = [t for t in TASKS if t.name in names]
    results = {}
    for model in sorted(p for p in run_dir.iterdir() if p.is_dir()):
        for mode in EXT:
            d = model / mode
            if d.is_dir():
                results[(model.name, mode)] = score_dir(d, mode, tasks)
    (run_dir / "scores.json").write_text(json.dumps({f"{m}/{l}": rows for (m, l), rows in results.items()}, indent=2))
    usage = json.loads((run_dir / "usage.json").read_text()) if (run_dir / "usage.json").exists() else {}
    md = summarize(results, usage)
    (run_dir / "scores.md").write_text(md + "\n")
    print(md)


if __name__ == "__main__":
    main()
