# gcd

Return the greatest common divisor of two **non-negative** 64-bit integers
`a` and `b`, with gcd(0, 0) = 0 and gcd(x, 0) = x. Inputs are any values in
`0..=i64::MAX`.

Keel signature: `fn gcd(a: i64, b: i64) -> i64`
Rust signature: `pub fn gcd(a: i64, b: i64) -> i64`
