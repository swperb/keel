pub fn midpoint(a: i64, b: i64) -> i64 {
    (((a as i128) + (b as i128)) >> 1) as i64
}
