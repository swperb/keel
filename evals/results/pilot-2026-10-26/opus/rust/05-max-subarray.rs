pub fn max_subarray(xs: &[i64]) -> i64 {
    let mut best: i64 = 0;
    let mut cur: i64 = 0;
    for &x in xs {
        cur += x;
        if cur < 0 {
            cur = 0;
        }
        if cur > best {
            best = cur;
        }
    }
    best
}
