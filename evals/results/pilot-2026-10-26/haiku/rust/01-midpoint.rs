pub fn midpoint(a: i64, b: i64) -> i64 {
    // Widen to i128 so the sum cannot overflow, then floor-divide by 2.
    (a as i128 + b as i128).div_euclid(2) as i64
}
