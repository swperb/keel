#!/usr/bin/env python3
"""Score agent solutions against hidden tests.

Layout:  evals/results/<run>/<model>/<lang>/<task>.{kl,rs}
         evals/results/<run>/<model>/<lang>/report.json   (agent's own notes)

Usage:   python3 evals/score.py <run-dir>      score a run
         python3 evals/score.py --ref          validate the harness with the reference solutions

For each solution we record:
  self_ok   the agent's own toolchain accepted it (keel check / rustc)
  outcome   pass | wrong | crash | unverified | harness_reject | compile_fail | missing
  silent    self_ok but the hidden tests did not pass: the dangerous case,
            where the agent had every reason to believe it was done
  proved    obligations the Keel verifier proved (machine-checked facts)
"""
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
KEEL = ROOT.parent / "target" / "release" / "keel"
TASKS = sorted(p for p in (ROOT / "tasks").iterdir() if p.is_dir())
EXT = {"keel": "kl", "rust": "rs"}
SPEC_WORDS = ("requires", "ensures", "invariant", "decreases", "assert", "spec fn", "lemma")


def run(cmd, timeout=120, stdin=None):
    try:
        p = subprocess.run([str(c) for c in cmd], capture_output=True, text=True, timeout=timeout, input=stdin)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return 124, "", "timeout"


def run_tests(binary, task):
    code, out, _ = run([binary], timeout=60)
    want = (task / "expected.txt").read_text().split()
    if code != 0:
        return "crash"
    return "pass" if out.split() == want else "wrong"


def score_keel(sol, task, work):
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
        return r
    r["outcome"] = run_tests(work / "t", task)
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


def score_dir(d, lang):
    rows = {}
    report = {}
    if (d / "report.json").exists():
        try:
            report = json.loads((d / "report.json").read_text())
        except json.JSONDecodeError:
            pass
    for task in TASKS:
        name = task.name.split("-", 1)[1].replace("-", "_")
        sol = d / f"{task.name}.{EXT[lang]}"
        if not sol.exists():
            rows[task.name] = {"outcome": "missing", "self_ok": False, "proved": 0, "contract_lines": 0}
            continue
        with tempfile.TemporaryDirectory() as w:
            rows[task.name] = (score_keel if lang == "keel" else score_rust)(sol, task, Path(w))
        rows[task.name]["iterations"] = report.get(task.name, {}).get("iterations")
        rows[task.name]["agent_confident"] = report.get(task.name, {}).get("confident")
        del name
    return rows


def summarize(results, usage=None):
    usage = usage or {}
    lines = ["| model | lang | pass | silent failures | not done | proved obligations | spec lines | avg toolchain runs | agent tokens | agent seconds |", "|---|---|---|---|---|---|---|---|---|---|"]
    for (model, lang), rows in sorted(results.items()):
        n = len(rows)
        passed = sum(r["outcome"] == "pass" for r in rows.values())
        silent = sum(r["self_ok"] and r["outcome"] != "pass" for r in rows.values())
        notdone = sum(not r["self_ok"] for r in rows.values())
        proved = sum(r["proved"] for r in rows.values())
        spec = sum(r["contract_lines"] for r in rows.values())
        its = [r.get("iterations") for r in rows.values() if isinstance(r.get("iterations"), (int, float))]
        avg = f"{sum(its) / len(its):.1f}" if its else "-"
        u = usage.get(f"{model}/{lang}", {})
        lines.append(f"| {model} | {lang} | {passed}/{n} | {silent} | {notdone} | {proved} | {spec} | {avg} | {u.get('tokens', '-')} | {u.get('seconds', '-')} |")
    lines.append("")
    lines.append("| model | lang | task | self_ok | outcome | proved | detail |")
    lines.append("|---|---|---|---|---|---|---|")
    for (model, lang), rows in sorted(results.items()):
        for t, r in rows.items():
            detail = ",".join(r.get("harness_codes", []) or r.get("self_codes", []))
            lines.append(f"| {model} | {lang} | {t} | {r['self_ok']} | {r['outcome']} | {r['proved']} | {detail} |")
    return "\n".join(lines)


def main():
    if len(sys.argv) == 2 and sys.argv[1] == "--ref":
        with tempfile.TemporaryDirectory() as tmp:
            results = {}
            for lang in EXT:
                d = Path(tmp) / lang
                d.mkdir()
                for task in TASKS:
                    (d / f"{task.name}.{EXT[lang]}").write_text((task / f"ref.{EXT[lang]}").read_text())
                results[("reference", lang)] = score_dir(d, lang)
        print(summarize(results))
        ok = all(r["outcome"] == "pass" for rows in results.values() for r in rows.values())
        sys.exit(0 if ok else 1)
    if len(sys.argv) != 2:
        print(__doc__)
        sys.exit(2)
    run_dir = Path(sys.argv[1])
    results = {}
    for model in sorted(p for p in run_dir.iterdir() if p.is_dir()):
        for lang in EXT:
            d = model / lang
            if d.is_dir():
                results[(model.name, lang)] = score_dir(d, lang)
    (run_dir / "scores.json").write_text(json.dumps({f"{m}/{l}": rows for (m, l), rows in results.items()}, indent=2))
    usage = json.loads((run_dir / "usage.json").read_text()) if (run_dir / "usage.json").exists() else {}
    md = summarize(results, usage)
    (run_dir / "scores.md").write_text(md + "\n")
    print(md)


if __name__ == "__main__":
    main()
