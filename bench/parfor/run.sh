#!/bin/sh
# Keel `par for` (OpenMP) vs Rust rayon on the same integer kernels.
# Prints wall-clock medians of 7 runs per configuration (whole process:
# allocation, kernel, serial checksum), after one warm-up run.
# Needs OpenMP for the parallel Keel build (on macOS: brew install libomp,
# or point KEEL_LIBOMP at a prefix with include/omp.h and lib/libomp.dylib).
set -eu
cd "$(dirname "$0")"
K=../../target/release/keel
OUT=$(mktemp -d)
(cd ../.. && cargo build --release -q)
(cd rayon_bench && cargo build --release -q)
R=rayon_bench/target/release/rayon_bench
for k in lcg triad logistic; do
  $K build $k.kl -o "$OUT/$k-omp" 2>"$OUT/$k.log" || { cat "$OUT/$k.log"; exit 1; }
  if grep -q "no OpenMP" "$OUT/$k.log"; then echo "keel built $k without OpenMP; parallel numbers would be serial" >&2; exit 1; fi
  KEEL_NO_OPENMP=1 $K build $k.kl -o "$OUT/$k-serial" 2>/dev/null
done
python3 - "$OUT" "$R" <<'PY'
import subprocess, sys, time, statistics, os
out, r = sys.argv[1], sys.argv[2]
def t(cmd):
    res = subprocess.run(cmd, capture_output=True, text=True, check=True)
    times = []
    for _ in range(7):
        s = time.perf_counter(); subprocess.run(cmd, capture_output=True, check=True); times.append(time.perf_counter() - s)
    return statistics.median(times), min(times), res.stdout.strip()
print(f"cores: {os.cpu_count()}")
print("| kernel | Keel par for (OpenMP) | Rust rayon | Keel serial | Rust serial | Keel / rayon |")
print("|---|---|---|---|---|---|")
for k in ["lcg", "triad", "logistic"]:
    kp, kps, ko = t([f"{out}/{k}-omp"])
    rp, rps, ro = t([r, k])
    ks, _, kso = t([f"{out}/{k}-serial"])
    rs, _, rso = t([r, k, "serial"])
    assert ko == ro == kso == rso, (k, ko, ro, kso, rso)
    print(f"| {k} | {kp:.3f} s | {rp:.3f} s | {ks:.3f} s | {rs:.3f} s | {kp/rp:.2f}x |")
    print(f"<!-- {k}: checksum {ko}; min parallel keel {kps:.3f} s, rayon {rps:.3f} s -->")
PY
rm -rf "$OUT"
