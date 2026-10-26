#!/bin/sh
# Keel test suite: examples must prove and print the expected output;
# every file in tests/reject must fail with the error code on its first line.
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
# Verification is deterministic: the same file gives byte-identical output.
a=$($K check examples/msort.kl 2>&1); b=$($K check examples/msort.kl 2>&1)
if [ "$a" = "$b" ]; then echo "ok   deterministic msort"; else echo "FAIL deterministic msort"; fail=1; fi
for f in examples/bad.kl examples/cheat.kl tests/reject/*.kl; do
  want=$(head -1 "$f" | sed -n 's#^// expect: ##p')
  out=$($K check "$f" 2>&1)
  if [ $? -ne 0 ] && echo "$out" | grep -q "error\[${want:-}"; then echo "ok   reject $f"; else echo "FAIL reject $f (want ${want:-any error})"; echo "$out" | head -3; fail=1; fi
done
exit $fail
