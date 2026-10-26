// The sort task of tree-bitonic (2^23 keys, same scan and checksum) by the
// same parallel mergesort as bench/keel/msort.kl: halves forked above 4096
// elements, merged through tmp.
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

fn merge(xs: &mut [u32], tmp: &mut [u32], mid: usize) {
    let (mut i, mut j) = (0, mid);
    for k in 0..xs.len() {
        if i < mid && (j == xs.len() || xs[i] <= xs[j]) {
            tmp[k] = xs[i];
            i += 1;
        } else {
            tmp[k] = xs[j];
            j += 1;
        }
    }
    xs.copy_from_slice(tmp);
}

fn msort(par: bool, xs: &mut [u32], tmp: &mut [u32]) {
    if xs.len() <= 1 {
        return;
    }
    let mid = xs.len() / 2;
    {
        let (x0, x1) = xs.split_at_mut(mid);
        let (t0, t1) = tmp.split_at_mut(mid);
        let p = par && x0.len() + x1.len() > 4096;
        join(p, || msort(par, x0, t0), || msort(par, x1, t1));
    }
    merge(xs, tmp, mid);
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
    let n = 1 << 23;
    let mut xs = vec![0u32; n];
    let mut tmp = vec![0u32; n];
    fill(par, &mut xs, 0);
    msort(par, &mut xs, &mut tmp);
    println!("{}", stat_out(scan(par, &xs)));
}
