pub fn first_index(xs: &[i64], key: i64) -> i64 {
    let mut lo: usize = 0;
    let mut hi: usize = xs.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if xs[mid] < key {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    if lo < xs.len() && xs[lo] == key {
        lo as i64
    } else {
        -1
    }
}
