# union

`a` and `b` are each sorted in non-decreasing order and may contain
duplicates. Write their sorted set union into `out`: every value that occurs
in `a` or in `b`, exactly once, in strictly increasing order, starting at
`out[0]`. Return the number of values written, `r`; the contents of
`out[r..]` do not matter. The caller guarantees `len(out) == len(a) + len(b)`.
Arrays may be empty; each input has length at most 1_000_000; elements are
any i64. O(len(a) + len(b)) time.

Keel signature: `fn union(a: &[i64], b: &[i64], out: &mut [i64]) -> i64`
Rust signature: `pub fn union(a: &[i64], b: &[i64], out: &mut [i64]) -> usize`
