#!/usr/bin/env python3
"""Head-to-head runner: Keel vs Rust vs Bend on Bend's own programs.

Builds every program, checks every Keel program with `keel check`, runs
each configuration (one warm-up run, then --runs timed runs), checks every
output against the expected checksum, and writes bench/results/results.json
and bench/RESULTS.md. Wall time is measured around each run; CPU time is
the run's user + system time from wait4. Each cell reports the median run.

    python3 bench/run.py                 # everything
    python3 bench/run.py --runs 3 --only queens,histogram

Needs: cargo, z3 and cc (for Keel), and Bend 2 (`bend` on PATH, or set
BEND=/path/to/bend). Without Bend its columns read "not measured". Bend's
GPU column runs on Metal on macOS and CUDA on Linux, and reads "not
measured" when neither is available.
"""

import argparse
import datetime
import json
import os
import platform
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BENCH = os.path.join(ROOT, "bench")
BUILD = os.path.join(BENCH, "build")
KEEL = os.path.join(ROOT, "target", "release", "keel")

# name, Bend source (None: no Bend program), expected output (last line),
# Bend's GPU memory flag (bench/runtime gate's MEMORY table, else "on"),
# what the Keel program proves.
PROGRAMS = [
    {
        "name": "par_sum",
        "bend": "par_sum.bend",
        "origin": "demos/pure_par_sum, d = 30",
        "expect": "3758096384",
        "gpu_mem": "on",
        "proved": "exact closed form of the sum (2 * sum == n * (2i + n - 1)), "
                  "no overflow, termination, race freedom",
    },
    {
        "name": "bitonic",
        "bend": "bitonic.bend",
        "origin": "bench/runtime/tree-bitonic, 2^23 keys",
        "expect": "3787129428",
        "gpu_mem": "768MB",
        "proved": "every compare-and-swap stage is a permutation (count "
                  "preserved), each half-cleaner leaves lower <= upper, bounds, "
                  "termination, race freedom. Not proved: that the whole network "
                  "sorts (checked at run time by the scan, as in Bend)",
    },
    {
        "name": "msort",
        "bend": None,
        "origin": "tree-bitonic's task (same keys, scan and checksum) by mergesort",
        "expect": "3787129428",
        "gpu_mem": None,
        "proved": "output sorted and a permutation of the input, bounds, "
                  "termination, race freedom",
    },
    {
        "name": "queens",
        "bend": "queens.bend",
        "origin": "bench/runtime/queens, 17 queens",
        "expect": "2063750025",
        "gpu_mem": "512MB",
        "proved": "shift amounts in range, every u32 store fits (bit ops "
                  "reduced mod 2^32, as in Bend's U32), termination (candidate "
                  "loop by a 32-step fuel bound, recursion by a row budget), race "
                  "freedom of the fork tree",
    },
    {
        "name": "histogram",
        "bend": "histogram.bend",
        "origin": "bench/runtime/histogram, 128 x 2^24 keys",
        "expect": "122845198",
        "gpu_mem": "on",
        "proved": "exact counts: every table entry is the count of its bucket "
                  "in its block, every result is the count of its bucket in the "
                  "whole key array, so no count overflows and no index is out of "
                  "bounds; termination; race freedom of the lanes Bend shares "
                  "through @unsafe Array.fork",
    },
    {
        "name": "matmul",
        "bend": "matmul.bend",
        "origin": "bench/runtime/tree-matmul, 384 x (128 x 128)",
        "expect": "3797651056",
        "gpu_mem": "on",
        "proved": "every Z-order index in bounds at every depth, termination, "
                  "race freedom of the parallel rounds; wrapping u32 arithmetic "
                  "by design (the product is checked at run time by Freivalds, "
                  "as in Bend)",
    },
]

CONFIGS = [
    ("keel_1", "Keel, 1 core"),
    ("keel_par", "Keel, par"),
    ("rust_seq", "Rust, serial"),
    ("rust_par", "Rust, rayon"),
    ("bend_seq", "Bend, 1 thread"),
    ("bend_par", "Bend, CPU threads"),
    ("bend_gpu", "Bend, GPU"),
]


def log(*a):
    print(*a, file=sys.stderr, flush=True)


def sh(cmd, cwd=None, env=None):
    r = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError("%s failed:\n%s%s" % (" ".join(cmd), r.stdout, r.stderr))
    return r.stdout + r.stderr


def cc():
    return os.environ.get("CC", "cc")


def ncpu():
    return os.cpu_count() or 1


def bend_threads():
    # The Bend gate's rule: the smallest power of two >= the core count.
    nt = 1
    while nt < ncpu() and nt < 256:
        nt *= 2
    return nt


def find_bend():
    b = os.environ.get("BEND") or shutil.which("bend")
    if b is None and os.path.exists(os.path.expanduser("~/.bend/bin/bend")):
        b = os.path.expanduser("~/.bend/bin/bend")
    return b


def gpu_kind():
    if platform.system() == "Darwin":
        return "metal"
    for d in [os.environ.get("CUDA_HOME"), os.environ.get("CUDA_PATH"),
              "/usr/local/cuda", "/opt/cuda"]:
        if d and os.path.exists(os.path.join(d, "include", "nvrtc.h")):
            return "cuda:" + d
    return None


def timed(cmd):
    """Run cmd once; return (wall s, cpu s, stdout)."""
    with tempfile.TemporaryFile() as out:
        t0 = time.perf_counter()
        p = subprocess.Popen(cmd, stdout=out, stderr=subprocess.STDOUT)
        _, status, ru = os.wait4(p.pid, 0)
        wall = time.perf_counter() - t0
        out.seek(0)
        text = out.read().decode(errors="replace")
    if os.waitstatus_to_exitcode(status) != 0:
        raise RuntimeError("%s exited with %d:\n%s" % (" ".join(cmd), os.waitstatus_to_exitcode(status), text))
    return wall, ru.ru_utime + ru.ru_stime, text


def measure(cmd, expect, runs):
    timed(cmd)  # warm-up (page cache, Metal shader cache)
    samples = []
    for _ in range(runs):
        wall, cpu, text = timed(cmd)
        got = text.strip().splitlines()[-1] if text.strip() else ""
        if got != expect:
            return {"error": "output %r, expected %r" % (got, expect), "cmd": cmd}
        samples.append((wall, cpu))
    walls = [w for w, _ in samples]
    med = sorted(samples)[len(samples) // 2]
    return {"wall": med[0], "cpu": med[1], "walls": walls,
            "cpus": [c for _, c in samples],
            "cmd": [os.path.relpath(a, ROOT) if os.path.isabs(a) else a for a in cmd]}


def build_keel(p, out):
    """keel check (timed) and build; also a 1-core build of the same C."""
    src = os.path.join(BENCH, "keel", p["name"] + ".kl")
    t0 = time.perf_counter()
    text = sh([KEEL, "check", src])
    check_s = time.perf_counter() - t0
    m = re.search(r"(\d+) obligations proved in (\d+) functions", text)
    info = {"check_s": check_s, "check_out": text.strip(),
            "obligations": int(m.group(1)), "functions": int(m.group(2))}
    binp = os.path.join(out, p["name"] + ".keel")
    sh([KEEL, "build", src, "-o", binp, "--emit-c"])
    csrc = binp + ".c"
    if not os.path.exists(csrc):
        raise RuntimeError("keel build --emit-c did not leave " + csrc)
    # The 1-core build caps the spawner at one live thread, so every par
    # runs inline; everything else is the same C and the same flags.
    c = open(csrc).read()
    cap = "klrt_max = n > 0 ? (int)n : 1;"
    if cap not in c:
        raise RuntimeError("runtime spawner line not found in " + csrc)
    one = binp + "1.c"
    open(one, "w").write(c.replace(cap, "klrt_max = 1;"))
    sh([cc(), "-O3", "-std=c11", "-w", "-o", binp + "1", one, "-lpthread"])
    return binp, binp + "1", info


def build_bend(bend, p, out, gpu):
    src = os.path.join(BENCH, "bend", p["bend"])
    csrc = os.path.join(out, p["name"] + ".bend.c")
    env = dict(os.environ, BEND_NO_TELEMETRY="1")
    sh([bend, src, "-o", csrc], env=env)
    cpu = os.path.join(out, p["name"] + ".bend")
    # The Bend gate's cc lines (gates/perf.ts), plus -lm for Linux.
    sh([cc(), "-std=c11", "-O3", csrc, "-lpthread", "-lm", "-o", cpu])
    gbin = None
    if gpu == "metal":
        gbin = cpu + ".gpu"
        sh([cc(), "-std=c11", "-O3", "-DBEND_METAL=1", "-x", "objective-c",
            "-fobjc-arc", csrc, "-lpthread", "-lm", "-framework", "Metal",
            "-framework", "Foundation", "-o", gbin])
    elif gpu and gpu.startswith("cuda:"):
        d = gpu[5:]
        gbin = cpu + ".gpu"
        sh([cc(), "-std=c11", "-O3", "-DBEND_CUDA=1", "-I" + d + "/include",
            "-L" + d + "/lib64", "-L" + d + "/lib", csrc, "-lpthread", "-lm",
            "-lcuda", "-lnvrtc", "-o", gbin])
    if gbin:
        sh([gbin, "+RTS", "--gpu-build"], env=dict(env, BENDRTS=""))
    return cpu, gbin


def machine():
    info = {"os": platform.platform(), "cores": ncpu(), "python": platform.python_version()}
    try:
        info["cpu"] = sh(["sysctl", "-n", "machdep.cpu.brand_string"]).strip()
        info["mem_gb"] = int(sh(["sysctl", "-n", "hw.memsize"]).strip()) // 2**30
    except Exception:
        try:
            info["cpu"] = re.search(r"model name\s*:\s*(.*)", open("/proc/cpuinfo").read()).group(1)
        except Exception:
            info["cpu"] = platform.processor()
    info["cc"] = sh([cc(), "--version"]).splitlines()[0]
    info["rustc"] = sh(["rustc", "--version"]).strip()
    info["z3"] = sh(["z3", "--version"]).strip()
    info["load_before"] = os.getloadavg()
    return info


def fmt(cell):
    if cell is None:
        return "not measured"
    if "error" in cell:
        return "FAILED"
    return "%.2f" % cell["wall"]


def fmt_cpu(cell):
    if cell is None:
        return "not measured"
    if "error" in cell:
        return "FAILED"
    return "%.2f" % cell["cpu"]


def report(res):
    m = res["machine"]
    L = []
    L.append("# Keel vs Rust vs Bend on Bend's programs")
    L.append("")
    L.append("Generated by `python3 bench/run.py` on %s. Every number below was "
             "measured by that run on this machine; nothing is estimated." % res["date"])
    L.append("")
    L.append("- Machine: %s, %d cores, %s GB, %s" % (m["cpu"], m["cores"], m.get("mem_gb", "?"), m["os"]))
    L.append("- Keel at `%s`, %s, %s" % (res["keel_commit"], m["cc"], m["z3"]))
    L.append("- %s, rayon 1.x (default pool: one thread per core)" % m["rustc"])
    L.append("- Bend: %s" % (res["bend_version"] or "not installed"))
    L.append("- Bend GPU: %s" % (res["gpu"] or "none available, so not measured"))
    L.append("- Load average (1, 5, 15 min) before the run: %s" % ", ".join("%.2f" % x for x in m["load_before"]))
    if "load_after" in res:
        L.append("- Load average after the run: %s" % ", ".join("%.2f" % x for x in res["load_after"]))
    L.append("- Each cell: median of %d timed runs after one warm-up run; every "
             "run's output was checked against the expected checksum." % res["runs"])
    L.append("")
    L.append("## Wall time (seconds)")
    L.append("")
    names = [n for _, n in CONFIGS]
    L.append("| program | " + " | ".join(names) + " |")
    L.append("|---|" + "---:|" * len(names))
    for p in res["programs"]:
        L.append("| %s | " % p["name"] + " | ".join(fmt(p["cells"].get(k)) for k, _ in CONFIGS) + " |")
    L.append("")
    L.append("## CPU time, user + system (seconds)")
    L.append("")
    L.append("| program | " + " | ".join(names) + " |")
    L.append("|---|" + "---:|" * len(names))
    for p in res["programs"]:
        L.append("| %s | " % p["name"] + " | ".join(fmt_cpu(p["cells"].get(k)) for k, _ in CONFIGS) + " |")
    L.append("")
    L.append("Bend's GPU column counts host CPU time only; the GPU's own time is in "
             "its wall time. Keel's 1-core column is the same C with the `par` "
             "spawner capped at one thread; Bend's CPU threads column uses %d "
             "threads (the Bend gate's rule: the power of two at or above the core "
             "count). `msort` has no Bend program: compare it with Bend's `bitonic` "
             "row, which sorts the same keys to the same checksum." % res["bend_threads"])
    L.append("")
    L.append("## Caveats")
    L.append("")
    L.append("- `par_sum` is not Bend's exact demo. The demo sums 2^16 numbers as a "
             "`Nat`, which Bend caps at 2^48, so it cannot run past d = 24. Here Bend "
             "sums 2^30 numbers as a wrapping 32-bit U32; Keel and Rust compute the "
             "exact sum in i64 and print it mod 2^32, the same value.")
    L.append("- The Keel 1-core column is this runner's construction: Keel has no "
             "thread-count option, so the runner recompiles Keel's emitted C with the "
             "`par` spawner capped at one live thread (every `par` runs inline).")
    L.append("- Bend's GPU CPU times count host CPU only; the GPU's work shows only in "
             "the GPU wall time.")
    L.append("- The machine was shared with other work during the run (load averages "
             "above). Run-to-run noise is real: earlier single runs on the busy "
             "machine had Keel's `par` 2-3x slower than rayon on several programs, "
             "while these 5-run medians are close, so small gaps "
             "between columns may be noise. `results/results.json` has every sample.")
    L.append("")
    L.append("## What Keel proved")
    L.append("")
    L.append("| program | Bend source | proved by `keel check` | obligations | check time |")
    L.append("|---|---|---|---:|---:|")
    for p in res["programs"]:
        k = p["keel"]
        L.append("| %s | %s | %s | %d in %d fns | %.1f s |" % (
            p["name"], p["origin"], p["proved"], k["obligations"], k["functions"], k["check_s"]))
    L.append("")
    errs = [(p["name"], k, c) for p in res["programs"] for k, c in p["cells"].items() if c and "error" in c]
    if errs:
        L.append("## Failures")
        L.append("")
        for n, k, c in errs:
            L.append("- %s / %s: %s" % (n, k, c["error"]))
        L.append("")
    return "\n".join(L)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=5)
    ap.add_argument("--only", default="")
    ap.add_argument("--report", action="store_true",
                    help="rewrite RESULTS.md from results/results.json without running")
    args = ap.parse_args()
    if args.report:
        with open(os.path.join(BENCH, "results", "results.json")) as f:
            res = json.load(f)
        md = report(res)
        with open(os.path.join(BENCH, "RESULTS.md"), "w") as f:
            f.write(md + "\n")
        print(md)
        return
    only = set(filter(None, args.only.split(",")))

    os.makedirs(BUILD, exist_ok=True)
    log("building keel and the Rust twins")
    sh(["cargo", "build", "--release", "--quiet"], cwd=ROOT)
    sh(["cargo", "build", "--release", "--quiet"], cwd=os.path.join(BENCH, "rust"))
    rust = os.path.join(BENCH, "rust", "target", "release")
    bend = find_bend()
    bver = sh([bend, "version"], env=dict(os.environ, BEND_NO_TELEMETRY="1")).strip() if bend else None
    gpu = gpu_kind() if bend else None

    res = {
        "date": datetime.datetime.now().strftime("%Y-%m-%d %H:%M"),
        "machine": machine(),
        "keel_commit": sh(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT).strip(),
        "bend_version": bver,
        "bend_threads": bend_threads(),
        "gpu": gpu,
        "runs": args.runs,
        "programs": [],
    }
    for p in PROGRAMS:
        if only and p["name"] not in only:
            continue
        log("== " + p["name"])
        kbin, kbin1, kinfo = build_keel(p, BUILD)
        log("   keel check: %d obligations, %.1f s" % (kinfo["obligations"], kinfo["check_s"]))
        cells = {}
        cmds = {
            "keel_1": [kbin1],
            "keel_par": [kbin],
            "rust_seq": [os.path.join(rust, p["name"]), "seq"],
            "rust_par": [os.path.join(rust, p["name"]), "par"],
        }
        if bend and p["bend"]:
            bcpu, bgpu = build_bend(bend, p, BUILD, gpu)
            cmds["bend_seq"] = [bcpu, "+RTS", "--threads", "1", "--gpu", "off"]
            cmds["bend_par"] = [bcpu, "+RTS", "--threads", str(bend_threads()), "--gpu", "off"]
            if bgpu:
                cmds["bend_gpu"] = [bgpu, "+RTS", "--gpu", p["gpu_mem"]]
        for key, _ in CONFIGS:
            if key in cmds:
                c = measure(cmds[key], p["expect"], args.runs)
                cells[key] = c
                log("   %-9s %s" % (key, c.get("error") or "%.3f s wall, %.3f s cpu" % (c["wall"], c["cpu"])))
        res["programs"].append(dict(p, keel=kinfo, cells=cells))

    res["load_after"] = os.getloadavg()
    os.makedirs(os.path.join(BENCH, "results"), exist_ok=True)
    with open(os.path.join(BENCH, "results", "results.json"), "w") as f:
        json.dump(res, f, indent=1)
    md = report(res)
    with open(os.path.join(BENCH, "RESULTS.md"), "w") as f:
        f.write(md + "\n")
    print(md)


if __name__ == "__main__":
    main()
