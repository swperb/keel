// Bend's bench/runtime/tree-bitonic at d = 23, as an array bitonic network
// with the same split points and cutoffs as bench/keel/bitonic.kl.
use keel_bench_rust::{join, parallel};

fn prng(x: u32) -> u32 {
    let b = x ^ (x << 13);
    let c = b ^ (b >> 17);
    c ^ (c << 5)
}

fn key(i: u32) -> u32 {
    prng(i.wrapping_add(1).wrapping_mul(2654435761))
}

fn fill(par: bool, xs: &mut [u32], base: u32) {
    if xs.len() <= 65536 {
        for (i, x) in xs.iter_mut().enumerate() {
            *x = key(base + i as u32);
        }
        return;
    }
    let h = xs.len() / 2;
    let (lo, hi) = xs.split_at_mut(h);
    join(par, || fill(par, lo, base), || fill(par, hi, base + h as u32));
}

fn cswap(par: bool, a: &mut [u32], b: &mut [u32], up: bool) {
    if a.len() <= 4096 {
        for (x, y) in a.iter_mut().zip(b.iter_mut()) {
            if (up && *x > *y) || (!up && *x < *y) {
                std::mem::swap(x, y);
            }
        }
        return;
    }
    let m = a.len() / 2;
    let (a0, a1) = a.split_at_mut(m);
    let (b0, b1) = b.split_at_mut(m);
    join(par, || cswap(par, a0, b0, up), || cswap(par, a1, b1, up));
}

fn bmerge(par: bool, xs: &mut [u32], d: u32, up: bool) {
    if d == 0 {
        return;
    }
    let h = xs.len() / 2;
    let (lo, hi) = xs.split_at_mut(h);
    cswap(par, lo, hi, up);
    let p = par && d > 12;
    join(p, || bmerge(par, lo, d - 1, up), || bmerge(par, hi, d - 1, up));
}

fn bsort(par: bool, xs: &mut [u32], d: u32, up: bool) {
    if d == 0 {
        return;
    }
    let h = xs.len() / 2;
    {
        let (lo, hi) = xs.split_at_mut(h);
        let p = par && d > 12;
        join(p, || bsort(par, lo, d - 1, true), || bsort(par, hi, d - 1, false));
    }
    bmerge(par, xs, d, up);
}

#[derive(Clone, Copy)]
struct Stat {
    lo: u32,
    hi: u32,
    ok: u32,
    mx: u32,
}

fn sjoin(a: Stat, b: Stat) -> Stat {
    Stat {
        lo: a.lo,
        hi: b.hi,
        ok: if a.hi <= b.lo { a.ok & b.ok } else { 0 },
        mx: a.mx.wrapping_mul(2654435761).wrapping_add(b.mx),
    }
}

fn scan(par: bool, xs: &[u32]) -> Stat {
    if xs.len() == 1 {
        return Stat { lo: xs[0], hi: xs[0], ok: 1, mx: xs[0] };
    }
    let h = xs.len() / 2;
    let p = par && xs.len() > 65536;
    let (a, b) = join(p, || scan(par, &xs[..h]), || scan(par, &xs[h..]));
    sjoin(a, b)
}

fn stat_out(s: Stat) -> u32 {
    (s.mx.wrapping_mul(2654435761) ^ s.hi.wrapping_add(s.lo.wrapping_mul(340573321)))
        .wrapping_add(s.ok.wrapping_mul(2246822519))
}

fn main() {
    let par = parallel();
    let d = 23;
    let mut xs = vec![0u32; 1 << d];
    fill(par, &mut xs, 0);
    bsort(par, &mut xs, d, true);
    println!("{}", stat_out(scan(par, &xs)));
}
