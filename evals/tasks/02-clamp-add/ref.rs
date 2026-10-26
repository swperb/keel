pub fn clamp_add(a: i64, b: i64, lo: i64, hi: i64) -> i64 {
    (a as i128 + b as i128).clamp(lo as i128, hi as i128) as i64
}
