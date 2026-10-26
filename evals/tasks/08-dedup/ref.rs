pub fn dedup(xs: &mut [i64]) -> usize {
    if xs.is_empty() {
        return 0;
    }
    let mut w = 1;
    for i in 1..xs.len() {
        if xs[i] != xs[w - 1] {
            xs[w] = xs[i];
            w += 1;
        }
    }
    w
}
