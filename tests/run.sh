#!/bin/sh
# Keel test suite: examples must prove and print the expected output;
# every file in tests/accept must prove; every file in tests/reject must fail
# with the error code on its first line.
set -u
cd "$(dirname "$0")/.."
K=./target/release/keel
fail=0
expect_run() {
  out=$($K run "examples/$1.kl" 2>/dev/null | tr '\n' ' ')
  if [ "$out" = "$2" ]; then echo "ok   run $1"; else echo "FAIL run $1: got '$out', want '$2'"; fail=1; fi
}
expect_run sum "7000 "
expect_run search "999999 -1 "
expect_run primes "1270607 "
expect_run shapes "7 100 12 0 "
expect_run proofs "3000 "
expect_run msort "311 1074053543 2147483573 "
expect_run bits "120 6 90 2176876992 -42 -5 12 "
expect_run sized "1964367075 57005 48879 3735928559 1 -400 4 -128 4000000000 "
# Narrow operands are computed in i64, never in C's int or uint32_t.
expect_run promote "9000000000000000000 -1 -200 "
# par for: the first and third lines count slots where the parallel result
# differs from a serial loop. The OpenMP build (when the C compiler has it)
# must also print exactly what the forced-serial build prints.
expect_run parfor "0 1073742784901088 0 5467600 424 -424 "
a=$($K run examples/parfor.kl 2>/dev/null); b=$(KEEL_NO_OPENMP=1 $K run examples/parfor.kl 2>/dev/null)
if [ -n "$a" ] && [ "$a" = "$b" ]; then echo "ok   parfor parallel == serial"; else echo "FAIL parfor parallel != serial"; fail=1; fi
# GPU backend coverage (docs/gpu.md). Where a GPU is present the default
# run uses it; KEEL_GPU=0 forces the CPU. tests/gpu.sh also requires that
# the kernels actually launched.
expect_run kernels "2258497628 2538369920 2545925184 3402507152 1018509904 122996 116 512646704 3206573824 "
a=$($K run examples/kernels.kl 2>/dev/null); b=$(KEEL_GPU=0 $K run examples/kernels.kl 2>/dev/null)
if [ -n "$a" ] && [ "$a" = "$b" ]; then echo "ok   kernels default == KEEL_GPU=0"; else echo "FAIL kernels default != KEEL_GPU=0"; fail=1; fi
# f32: parallel and serial results agree bit for bit (first and third
# lines), and float-to-integer conversion is defined for every input.
expect_run f32 "0 412565504 0 2624117011 -2 9223372036854775807 -9223372036854775808 0 9223372036854775807 16777216 1065353216 1 0 "
# Verification is deterministic: the same file gives byte-identical output.
a=$($K check examples/msort.kl 2>&1); b=$($K check examples/msort.kl 2>&1)
if [ "$a" = "$b" ]; then echo "ok   deterministic msort"; else echo "FAIL deterministic msort"; fail=1; fi
for f in tests/accept/*.kl; do
  if out=$($K check "$f" 2>&1); then echo "ok   accept $f"; else echo "FAIL accept $f"; echo "$out" | head -3; fail=1; fi
done
# A function's query carries only the spec fn definitions it uses (#4).
d=$(mktemp -d); $K check --dump-smt "$d" tests/accept/unused_spec_isolated.kl >/dev/null 2>&1
if [ -f "$d/groups.smt2" ] && ! grep -q "(sf.first p" "$d/groups.smt2" && grep -q "(sf.prefix p" "$d/groups.smt2"; then echo "ok   unused spec fn left out of query"; else echo "FAIL unused spec fn left out of query"; fail=1; fi
rm -rf "$d"
for f in examples/bad.kl examples/cheat.kl tests/reject/*.kl; do
  want=$(head -1 "$f" | sed -n 's#^// expect: ##p')
  out=$($K check "$f" 2>&1)
  if [ $? -ne 0 ] && echo "$out" | grep -q "error\[${want:-}"; then echo "ok   reject $f"; else echo "FAIL reject $f (want ${want:-any error})"; echo "$out" | head -3; fail=1; fi
done
exit $fail
