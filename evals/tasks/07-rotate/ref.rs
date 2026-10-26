pub fn rotate(xs: &mut [i64], k: i64) {
    let n = xs.len() as i64;
    if n == 0 {
        return;
    }
    xs.rotate_right(k.rem_euclid(n) as usize);
}
