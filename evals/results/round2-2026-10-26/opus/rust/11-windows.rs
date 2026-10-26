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
    if w < 1 || w > xs.len() as i64 {
        return i64::MIN;
    }
    let w = w as usize;
    let mut s: i64 = xs[..w].iter().sum();
    let mut best = s;
    for i in w..xs.len() {
        s += xs[i] - xs[i - w];
        if s > best {
            best = s;
        }
    }
    best
}
