pub fn clamp_add(a: i64, b: i64, lo: i64, hi: i64) -> i64 {
    let s = a as i128 + b as i128;
    if s < lo as i128 {
        lo
    } else if s > hi as i128 {
        hi
    } else {
        s as i64
    }
}
