# windows (three functions)

Write three functions over an array `xs` with `len(xs) <= 1_000_000` and
every element in `-1_000_000_000..=1_000_000_000`. Arrays may be empty.

1. `prefix(xs, pre)`: the caller passes `pre` with `len(pre) == len(xs) + 1`.
   Fill it with prefix sums: `pre[k]` is the sum of `xs[0..k]` (so
   `pre[0] == 0`).
2. `range_sum(xs, pre, lo, hi)`: `pre` holds the prefix sums of `xs` as
   produced by `prefix`, and `0 <= lo <= hi <= len(xs)`. Return the sum of
   `xs[lo..hi]` in O(1).
3. `best_window(xs, w)`: return the largest sum of any contiguous window of
   exactly `w` elements. If there is no such window (`w < 1` or
   `w > len(xs)`), return `-9223372036854775808` (i64::MIN). O(n) time.

The hidden tests call `range_sum` on the `pre` that your `prefix` produced, so
in Keel the contracts of the two must fit together.

Keel signatures:
```
fn prefix(xs: &[i64], pre: &mut [i64])
fn range_sum(xs: &[i64], pre: &[i64], lo: i64, hi: i64) -> i64
fn best_window(xs: &[i64], w: i64) -> i64
```
Rust signatures:
```rust
pub fn prefix(xs: &[i64], pre: &mut [i64])
pub fn range_sum(xs: &[i64], pre: &[i64], lo: usize, hi: usize) -> i64
pub fn best_window(xs: &[i64], w: i64) -> i64
```
