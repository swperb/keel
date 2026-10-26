# rotate

Rotate `xs` to the right by `k` positions, in place: the element at index
`j` moves to index `(j + k) mod n`, where `n` is the length and `mod` is the
mathematical (always non-negative) remainder. `k` may be any i64, including
negative values (rotate left) and values larger than `n`. Arrays may be empty
and have length at most 1_000_000; elements are any i64. O(n) time.

Keel: `orig` is a read-only copy of the initial contents of `xs`, passed by
the caller so that specifications can refer to the input (Keel has no
`old(...)`). The caller guarantees `len(orig) == len(xs)` and
`orig[i] == xs[i]` for every `i` on entry, and `len(xs) <= 1_000_000`.

Keel signature: `fn rotate(xs: &mut [i64], k: i64, orig: &[i64])`
Rust signature: `pub fn rotate(xs: &mut [i64], k: i64)`
