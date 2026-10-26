# midpoint

Return the floor of the mathematical average of `a` and `b`, that is
floor((a + b) / 2) computed exactly, for **every** pair of 64-bit signed
integers. Examples: midpoint(3, 4) = 3, midpoint(-3, -4) = -4,
midpoint(-1, 0) = -1, midpoint(i64::MAX, i64::MAX) = i64::MAX.

Keel signature: `fn midpoint(a: i64, b: i64) -> i64`
Rust signature: `pub fn midpoint(a: i64, b: i64) -> i64`
