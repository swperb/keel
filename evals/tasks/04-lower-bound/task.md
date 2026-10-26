# first_index

`xs` is sorted in non-decreasing order and may contain duplicates. Return the
**smallest** index `i` with `xs[i] == key`, or -1 if `key` does not occur.
Must run in O(log n). Arrays may be empty and may hold any i64 values.

Keel signature: `fn first_index(xs: &[i64], key: i64) -> i64`
Rust signature: `pub fn first_index(xs: &[i64], key: i64) -> i64`
