pub fn partition(xs: &mut [i64], p: i64) -> usize {
    let mut lo: Vec<i64> = Vec::with_capacity(xs.len());
    let mut hi: Vec<i64> = Vec::new();
    for &x in xs.iter() {
        if x < p {
            lo.push(x);
        } else {
            hi.push(x);
        }
    }
    let c = lo.len();
    xs[..c].copy_from_slice(&lo);
    xs[c..].copy_from_slice(&hi);
    c
}
