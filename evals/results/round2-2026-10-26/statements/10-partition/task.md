# partition (stable)

Rearrange `xs` in place so that every element less than `p` comes before
every element greater than or equal to `p`, keeping the original relative
order within each group (a stable partition). Return the number of elements
less than `p`. Arrays may be empty and have length at most 1_000_000;
elements and `p` are any i64. O(n) time; O(n) extra space is allowed.

Example: `xs = [3, -1, 4, 1, -5, 9, 2, 6]`, `p = 3` gives
`[-1, 1, -5, 2, 3, 4, 9, 6]` and returns 4.

Keel: `orig` is a read-only copy of the initial contents of `xs`, passed by
the caller so that specifications can refer to the input (Keel has no
`old(...)`). The caller guarantees `len(orig) == len(xs)` and
`orig[i] == xs[i]` for every `i` on entry, and `len(xs) <= 1_000_000`.

Keel signature: `fn partition(xs: &mut [i64], p: i64, orig: &[i64]) -> i64`
Rust signature: `pub fn partition(xs: &mut [i64], p: i64) -> usize`
