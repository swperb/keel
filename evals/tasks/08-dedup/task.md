# dedup

`xs` is sorted in non-decreasing order. Remove duplicates in place: move the
distinct values to the front of `xs` in increasing order and return how
many there are, `r`. Afterwards `xs[0..r]` holds each distinct value of the
input exactly once, in increasing order; the contents of `xs[r..]` do not
matter. Arrays may be empty and have length at most 1_000_000; elements are
any i64. O(n) time.

Keel: `orig` is a read-only copy of the initial contents of `xs`, passed by
the caller so that specifications can refer to the input (Keel has no
`old(...)`). The caller guarantees `len(orig) == len(xs)` and
`orig[i] == xs[i]` for every `i` on entry, and `len(xs) <= 1_000_000`.

Keel signature: `fn dedup(xs: &mut [i64], orig: &[i64]) -> i64`
Rust signature: `pub fn dedup(xs: &mut [i64]) -> usize`
