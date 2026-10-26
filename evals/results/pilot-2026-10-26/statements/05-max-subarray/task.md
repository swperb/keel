# max_subarray

Return the largest sum of any contiguous subarray of `xs`. The empty
subarray counts (sum 0), so the answer is never negative. Inputs satisfy:
`len(xs) <= 1_000_000` and every element is in `-1_000_000..=1_000_000`.
Must run in O(n).

Keel signature: `fn max_subarray(xs: &[i64]) -> i64`
Rust signature: `pub fn max_subarray(xs: &[i64]) -> i64`
