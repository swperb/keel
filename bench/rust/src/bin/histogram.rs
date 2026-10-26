// Bend's bench/runtime/histogram (D = 24, B = 11, R = 128), same blocks,
// table layout and fork points as bench/keel/histogram.kl.
use keel_bench_rust::{join, parallel};

fn prng(x: u32) -> u32 {
    let b = x ^ (x << 13);
    let c = b ^ (b >> 17);
    c ^ (c << 5)
}

fn fill(par: bool, xs: &mut [u32], base: u32, s: u32) {
    if xs.len() <= 8192 {
        for (i, x) in xs.iter_mut().enumerate() {
            *x = prng(prng((base + i as u32 + 1).wrapping_mul(2654435761).wrapping_add(s))) & 255;
        }
        return;
    }
    let h = xs.len() / 2;
    let (lo, hi) = xs.split_at_mut(h);
    join(par, || fill(par, lo, base, s), || fill(par, hi, base + h as u32, s));
}

fn count_block(keys: &[u32], row: &mut [u32]) {
    row.fill(0);
    for &k in keys {
        row[k as usize] += 1;
    }
}

fn rows(par: bool, keys: &[u32], t: &mut [u32], nb: usize) {
    if nb == 1 {
        count_block(keys, t);
        return;
    }
    let h = nb / 2;
    let (k0, k1) = keys.split_at(h * 8192);
    let (t0, t1) = t.split_at_mut(h * 256);
    join(par, || rows(par, k0, t0, h), || rows(par, k1, t1, nb - h));
}

fn cols(par: bool, t: &[u32], nb: usize, cs: &mut [u32], c0: usize) {
    if cs.len() <= 16 {
        for (c, out) in cs.iter_mut().enumerate() {
            let mut s = 0u32;
            for g in 0..nb {
                s += t[g * 256 + c0 + c];
            }
            *out = s;
        }
        return;
    }
    let h = cs.len() / 2;
    let (a, b) = cs.split_at_mut(h);
    join(par, || cols(par, t, nb, a, c0), || cols(par, t, nb, b, c0 + h));
}

fn main() {
    let par = parallel();
    let nb = 2048;
    let mut keys = vec![0u32; 1 << 24];
    let mut t = vec![0u32; nb * 256];
    let mut cs = vec![0u32; 256];
    let mut h = 0u32;
    for r in 0..128u32 {
        fill(par, &mut keys, 0, 7 + r);
        rows(par, &keys, &mut t, nb);
        cols(par, &t, nb, &mut cs, 0);
        for &c in &cs {
            h = h.wrapping_mul(2654435761) ^ c;
        }
    }
    println!("{}", h);
}
