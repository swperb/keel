#!/bin/sh
# Keel par for on an NVIDIA GPU vs the same program on the CPU (OpenMP and
# serial) vs Rust rayon, on one Linux machine. Wall-clock medians of 7
# whole-process runs after a warm-up, plus the GPU time split from
# KEEL_GPU_TIMING (copies to and from the device, kernel).
set -eu
cd "$(dirname "$0")"
K=../../target/release/keel
OUT=$(mktemp -d)
(cd ../.. && cargo build --release -q)
(cd rayon_bench && cargo build --release -q)
R=rayon_bench/target/release/rayon_bench
for k in lcg triad logistic; do
  $K build $k.kl -o "$OUT/$k" 2>/dev/null
  KEEL_NO_OPENMP=1 $K build $k.kl -o "$OUT/$k-serial" 2>/dev/null
done
nvidia-smi --query-gpu=name,driver_version --format=csv,noheader
python3 - "$OUT" "$R" <<'PY'
import subprocess, sys, time, statistics, os, re
out, r = sys.argv[1], sys.argv[2]
def t(cmd, env={}):
    e = dict(os.environ, **env)
    res = subprocess.run(cmd, capture_output=True, text=True, check=True, env=e)
    times = []
    for _ in range(7):
        s = time.perf_counter(); subprocess.run(cmd, capture_output=True, check=True, env=e); times.append(time.perf_counter() - s)
    return statistics.median(times), res.stdout.strip()
print(f"cpu threads: {os.cpu_count()}")
print("| kernel | Keel GPU | Keel CPU (OpenMP) | Keel serial | Rust rayon | GPU: copy in / kernel / copy out (sum over launches) |")
print("|---|---|---|---|---|---|")
for k in ["lcg", "triad", "logistic"]:
    g, go = t([f"{out}/{k}"], {"KEEL_GPU": "1"})
    c, co = t([f"{out}/{k}"], {"KEEL_GPU": "0"})
    s, so = t([f"{out}/{k}-serial"], {"KEEL_GPU": "0"})
    rr, ro = t([r, k])
    assert go == co == so == ro, (k, go, co, so, ro)
    log = subprocess.run([f"{out}/{k}"], capture_output=True, text=True, env=dict(os.environ, KEEL_GPU="1", KEEL_GPU_TIMING="1")).stderr
    parts = [sum(float(x) for x in re.findall(p + r" ([0-9.]+) ms", log)) for p in ["copy in", "kernel", "copy out"]]
    n = len(re.findall(r"ok:", log))
    print(f"| {k} | {g:.3f} s | {c:.3f} s | {s:.3f} s | {rr:.3f} s | {parts[0]:.1f} / {parts[1]:.1f} / {parts[2]:.1f} ms ({n} launches) |")
PY
rm -rf "$OUT"
