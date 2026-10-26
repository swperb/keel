pub fn prefix(xs: &[i64], pre: &mut [i64]) {
    pre[0] = 0;
    for i in 0..xs.len() {
        pre[i + 1] = pre[i] + xs[i];
    }
}

pub fn range_sum(_xs: &[i64], pre: &[i64], lo: usize, hi: usize) -> i64 {
    pre[hi] - pre[lo]
}

pub fn best_window(xs: &[i64], w: i64) -> i64 {
    let n = xs.len() as i64;
    if w < 1 || w > n {
        return i64::MIN;
    }
    let w = w as usize;
    let mut pre = vec![0; xs.len() + 1];
    prefix(xs, &mut pre);
    (0..=xs.len() - w).map(|s| range_sum(xs, &pre, s, s + w)).max().unwrap()
}
