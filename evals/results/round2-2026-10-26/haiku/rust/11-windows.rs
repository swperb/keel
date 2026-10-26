pub fn prefix(xs: &[i64], pre: &mut [i64]) {
    pre[0] = 0;
    for k in 0..xs.len() {
        pre[k + 1] = pre[k] + xs[k];
    }
}

pub fn range_sum(_xs: &[i64], pre: &[i64], lo: usize, hi: usize) -> i64 {
    pre[hi] - pre[lo]
}

pub fn best_window(xs: &[i64], w: i64) -> i64 {
    let n = xs.len();
    if w < 1 || w as u64 > n as u64 {
        return i64::MIN;
    }
    let w = w as usize;
    let mut cur: i64 = xs[..w].iter().sum();
    let mut best = cur;
    for i in w..n {
        cur += xs[i] - xs[i - w];
        if cur > best {
            best = cur;
        }
    }
    best
}
