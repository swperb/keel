pub fn partition(xs: &mut [i64], p: i64) -> usize {
    let mut ge: Vec<i64> = Vec::new();
    let mut w = 0usize;
    for i in 0..xs.len() {
        let x = xs[i];
        if x < p {
            xs[w] = x;
            w += 1;
        } else {
            ge.push(x);
        }
    }
    xs[w..].copy_from_slice(&ge);
    w
}
