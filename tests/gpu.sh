#!/bin/sh
# GPU differential tests; run on a machine with an NVIDIA GPU and driver
# (from elsewhere: KEEL_GPU_HOST=user@host tools/gpu-remote.sh ./tests/gpu.sh).
# Each program must launch its kernels on the GPU without a failure and
# print exactly what the CPU build (KEEL_GPU=0) prints.
set -u
cd "$(dirname "$0")/.."
K=./target/release/keel
fail=0
d=$(mktemp -d)
for f in examples/kernels.kl examples/parfor.kl tests/gpu/cpu_only.kl bench/parfor/lcg.kl bench/parfor/triad.kl; do
  $K build "$f" -o "$d/p" 2>"$d/build" || { echo "FAIL build $f"; cat "$d/build"; fail=1; continue; }
  gpu=$(KEEL_GPU=1 KEEL_GPU_TIMING=1 "$d/p" 2>"$d/err"); cpu=$(KEEL_GPU=0 "$d/p" 2>/dev/null)
  launches=$(grep -c "^keel: gpu .* ok:" "$d/err")
  if [ "$launches" -gt 0 ] && ! grep -q "FAILED\|keel: note" "$d/err" && [ -n "$gpu" ] && [ "$gpu" = "$cpu" ]; then
    echo "ok   gpu $f ($launches launches, output equals CPU)"
  else
    echo "FAIL gpu $f"; head -5 "$d/err"; echo "gpu: $gpu" | head -3; echo "cpu: $cpu" | head -3; fail=1
  fi
done
$K build tests/gpu/cpu_only.kl -o "$d/p" 2>"$d/build"
if grep -q "line 9:3 runs on the CPU only: its body uses 's' of type Scale" "$d/build" && [ "$(grep -c 'CPU only' "$d/build")" = 1 ]; then
  echo "ok   gpu struct body stays on the CPU, the other loop does not"
else
  echo "FAIL gpu cpu_only note"; cat "$d/build"; fail=1
fi
rm -rf "$d"
exit $fail
