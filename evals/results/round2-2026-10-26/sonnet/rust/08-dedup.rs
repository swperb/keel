pub fn dedup(xs: &mut [i64]) -> usize {
    if xs.is_empty() {
        return 0;
    }
    let mut r = 1;
    for i in 1..xs.len() {
        if xs[i] != xs[r - 1] {
            xs[r] = xs[i];
            r += 1;
        }
    }
    r
}
