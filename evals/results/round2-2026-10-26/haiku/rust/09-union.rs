pub fn union(a: &[i64], b: &[i64], out: &mut [i64]) -> usize {
    let (mut i, mut j, mut r) = (0usize, 0usize, 0usize);
    while i < a.len() || j < b.len() {
        let v = if j >= b.len() || (i < a.len() && a[i] <= b[j]) {
            let v = a[i];
            i += 1;
            v
        } else {
            let v = b[j];
            j += 1;
            v
        };
        if r == 0 || out[r - 1] != v {
            out[r] = v;
            r += 1;
        }
    }
    r
}
