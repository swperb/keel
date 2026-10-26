// Bend's bench/runtime/tree-matmul (128 x 128, 384 rounds), with the same
// Z-order arrays, recursion and fork points as bench/keel/matmul.kl.
use keel_bench_rust::{join, parallel};

fn mat_gen(m: &mut [u32], d: u32, s: u32) {
    if d == 0 {
        m[0] = s % 100;
        return;
    }
    let q = m.len() / 4;
    let (m0, rest) = m.split_at_mut(q);
    let (m1, rest) = rest.split_at_mut(q);
    let (m2, m3) = rest.split_at_mut(q);
    mat_gen(m0, d - 1, s.wrapping_mul(1664525).wrapping_add(1));
    mat_gen(m1, d - 1, s.wrapping_mul(214013).wrapping_add(3));
    mat_gen(m2, d - 1, s.wrapping_mul(16843009).wrapping_add(5));
    mat_gen(m3, d - 1, s.wrapping_mul(48271).wrapping_add(7));
}

fn vec_gen(v: &mut [u32], d: u32, s: u32) {
    if d == 0 {
        v[0] = s.wrapping_mul(2654435761) % 100 + 1;
        return;
    }
    let h = v.len() / 2;
    let (v0, v1) = v.split_at_mut(h);
    vec_gen(v0, d - 1, s.wrapping_mul(1664525).wrapping_add(1));
    vec_gen(v1, d - 1, s.wrapping_mul(214013).wrapping_add(3));
}

fn quads(m: &[u32]) -> [&[u32]; 4] {
    let q = m.len() / 4;
    [&m[..q], &m[q..2 * q], &m[2 * q..3 * q], &m[3 * q..]]
}

fn mul_add(a: &[u32], b: &[u32], c: &mut [u32], d: u32) {
    if d == 0 {
        c[0] = c[0].wrapping_add(a[0].wrapping_mul(b[0]));
        return;
    }
    let [a0, a1, a2, a3] = quads(a);
    let [b0, b1, b2, b3] = quads(b);
    let q = c.len() / 4;
    let (c0, rest) = c.split_at_mut(q);
    let (c1, rest) = rest.split_at_mut(q);
    let (c2, c3) = rest.split_at_mut(q);
    mul_add(a0, b0, c0, d - 1);
    mul_add(a1, b2, c0, d - 1);
    mul_add(a0, b1, c1, d - 1);
    mul_add(a1, b3, c1, d - 1);
    mul_add(a2, b0, c2, d - 1);
    mul_add(a3, b2, c2, d - 1);
    mul_add(a2, b1, c3, d - 1);
    mul_add(a3, b3, c3, d - 1);
}

fn mv_add(m: &[u32], v: &[u32], o: &mut [u32], d: u32) {
    if d == 0 {
        o[0] = o[0].wrapping_add(m[0].wrapping_mul(v[0]));
        return;
    }
    let [m0, m1, m2, m3] = quads(m);
    let h = v.len() / 2;
    let (v0, v1) = v.split_at(h);
    let (o0, o1) = o.split_at_mut(h);
    mv_add(m0, v0, o0, d - 1);
    mv_add(m1, v1, o0, d - 1);
    mv_add(m2, v0, o1, d - 1);
    mv_add(m3, v1, o1, d - 1);
}

fn round(s: u32) -> u32 {
    let d = 7;
    let (n, k) = (1 << (2 * d), 1 << d);
    let mut a = vec![0u32; n];
    let mut b = vec![0u32; n];
    let mut c = vec![0u32; n];
    let mut r = vec![0u32; k];
    let mut t1 = vec![0u32; k];
    let mut u = vec![0u32; k];
    let mut t2 = vec![0u32; k];
    mat_gen(&mut a, d, s.wrapping_add(1));
    mat_gen(&mut b, d, s.wrapping_add(2));
    vec_gen(&mut r, d, s.wrapping_add(3));
    mul_add(&a, &b, &mut c, d);
    let ck = c.iter().fold(0u32, |x, &y| x.wrapping_add(y));
    mv_add(&c, &r, &mut t1, d);
    mv_add(&b, &r, &mut u, d);
    mv_add(&a, &u, &mut t2, d);
    (ck ^ s.wrapping_mul(2654435761)).wrapping_add((t1 == t2) as u32)
}

fn batch(par: bool, bg: u32, i: u32) -> u32 {
    if bg == 0 {
        let p = i.wrapping_mul(2654435761) & 511;
        return if p < 384 { round(p.wrapping_mul(2654435761)) } else { 0 };
    }
    let h = 1 << (bg - 1);
    let (x, y) = join(par, || batch(par, bg - 1, i), || batch(par, bg - 1, i + h));
    x.wrapping_add(y)
}

fn main() {
    let par = parallel();
    println!("{}", batch(par, 9, 0));
}
