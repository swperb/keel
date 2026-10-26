pub fn dedup(xs: &mut [i64]) -> usize {
    let n = xs.len();
    if n == 0 {
        return 0;
    }
    let mut w = 1usize;
    for i in 1..n {
        let x = xs[i];
        if x != xs[w - 1] {
            xs[w] = x;
            w += 1;
        }
    }
    w
}
