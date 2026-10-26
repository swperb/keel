pub fn partition(xs: &mut [i64], p: i64) -> usize {
    let lo: Vec<i64> = xs.iter().copied().filter(|&x| x < p).collect();
    let hi: Vec<i64> = xs.iter().copied().filter(|&x| x >= p).collect();
    xs[..lo.len()].copy_from_slice(&lo);
    xs[lo.len()..].copy_from_slice(&hi);
    lo.len()
}
