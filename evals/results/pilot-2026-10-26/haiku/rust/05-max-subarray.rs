pub fn max_subarray(xs: &[i64]) -> i64 {
    // Kadane's algorithm, with the empty subarray (0) allowed as a floor.
    let mut best: i64 = 0;
    let mut cur: i64 = 0;
    for &x in xs {
        cur = if cur + x > 0 { cur + x } else { 0 };
        if cur > best {
            best = cur;
        }
    }
    best
}
