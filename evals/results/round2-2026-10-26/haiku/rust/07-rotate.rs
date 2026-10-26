pub fn rotate(xs: &mut [i64], k: i64) {
    let n = xs.len();
    if n == 0 {
        return;
    }
    let s = k.rem_euclid(n as i64) as usize;
    xs.rotate_right(s);
}
