pub fn max_subarray(xs: &[i64]) -> i64 {
    let (mut best, mut cur) = (0i64, 0i64);
    for &x in xs { cur = (cur + x).max(0); best = best.max(cur); }
    best
}
