# clamp_add

Given 64-bit signed integers `a`, `b`, `lo`, `hi` with `lo <= hi`, return
the mathematically exact sum `a + b` clamped into `[lo, hi]`: `lo` if the
sum is below `lo`, `hi` if above `hi`, otherwise the sum. It must be correct
for **every** input with `lo <= hi`, including sums that do not fit in 64
bits (the clamp is of the exact sum, not a wrapped one).

Keel signature: `fn clamp_add(a: i64, b: i64, lo: i64, hi: i64) -> i64`
Rust signature: `pub fn clamp_add(a: i64, b: i64, lo: i64, hi: i64) -> i64`
