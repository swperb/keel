pub fn clamp_add(a: i64, b: i64, lo: i64, hi: i64) -> i64 {
    // The exact sum fits in i128; clamp it in that wider type.
    let s = a as i128 + b as i128;
    let l = lo as i128;
    let h = hi as i128;
    let c = if s < l {
        l
    } else if s > h {
        h
    } else {
        s
    };
    c as i64
}
