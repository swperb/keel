pub fn union(a: &[i64], b: &[i64], out: &mut [i64]) -> usize {
    let (mut i, mut j, mut w) = (0, 0, 0);
    while i < a.len() || j < b.len() {
        let v = if j >= b.len() || (i < a.len() && a[i] <= b[j]) {
            i += 1;
            a[i - 1]
        } else {
            j += 1;
            b[j - 1]
        };
        if w == 0 || out[w - 1] != v {
            out[w] = v;
            w += 1;
        }
    }
    w
}
