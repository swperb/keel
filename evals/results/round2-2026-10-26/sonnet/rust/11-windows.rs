pub fn prefix(xs: &[i64], pre: &mut [i64]) {
    let mut s = 0i64;
    pre[0] = 0;
    for (i, &x) in xs.iter().enumerate() {
        s += x;
        pre[i + 1] = s;
    }
}

pub fn range_sum(_xs: &[i64], pre: &[i64], lo: usize, hi: usize) -> i64 {
    pre[hi] - pre[lo]
}

pub fn best_window(xs: &[i64], w: i64) -> i64 {
    if w < 1 || (w as u64) > xs.len() as u64 {
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
