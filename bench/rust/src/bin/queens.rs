// Bend's bench/runtime/queens (17 queens, 2^17-leaf fork tree), same
// algorithm and fork points as bench/keel/queens.kl.
use keel_bench_rust::{join, parallel};

#[derive(Clone, Copy)]
struct Stats {
    sols: u32,
    nodes: u32,
}

fn solve(cand: u32, cols: u32, ld: u32, rd: u32, full: u32, mut sols: u32, mut nodes: u32) -> Stats {
    let mut c = cand;
    while c != 0 {
        let bit = c & c.wrapping_neg();
        let nc = cols | bit;
        if nc == full {
            sols = sols.wrapping_add(1);
            nodes = nodes.wrapping_add(1);
        } else {
            let nl = (ld | bit) << 1;
            let nr = (rd | bit) >> 1;
            let w = solve(full & !(nc | nl | nr), nc, nl, nr, full, sols, nodes.wrapping_add(1));
            sols = w.sols;
            nodes = w.nodes;
        }
        c -= bit;
    }
    Stats { sols, nodes }
}

const ZERO: Stats = Stats { sols: 0, nodes: 0 };

fn pfx(j: u32, nn: u32, full: u32, bound: u32) -> Stats {
    let i = j.wrapping_mul(2654435761) & 131071;
    if i >= bound {
        return ZERO;
    }
    let nn2 = nn * nn;
    let b0 = 1u32 << (i / (nn2 * nn));
    let b1 = 1u32 << ((i / nn2) % nn);
    if b1 & (b0 | (b0 << 1) | (b0 >> 1)) != 0 {
        return ZERO;
    }
    let b2 = 1u32 << ((i / nn) % nn);
    let c2 = b0 | b1;
    let l2 = ((b0 << 1) | b1) << 1;
    let r2 = ((b0 >> 1) | b1) >> 1;
    if b2 & (c2 | l2 | r2) != 0 {
        return ZERO;
    }
    let b3 = 1u32 << (i % nn);
    let c3 = c2 | b2;
    let l3 = (l2 | b2) << 1;
    let r3 = (r2 | b2) >> 1;
    if b3 & (c3 | l3 | r3) != 0 {
        return ZERO;
    }
    let c4 = c3 | b3;
    let l4 = (l3 | b3) << 1;
    let r4 = (r3 | b3) >> 1;
    solve(full & !(c4 | l4 | r4), c4, l4, r4, full, 0, 0)
}

fn merge(a: Stats, b: Stats) -> Stats {
    Stats { sols: a.sols.wrapping_add(b.sols), nodes: a.nodes.wrapping_add(b.nodes) }
}

fn batch(par: bool, d: u32, i: u32, nn: u32, full: u32, bound: u32) -> Stats {
    if d == 0 {
        return pfx(i, nn, full, bound);
    }
    let h = 1 << (d - 1);
    let p = par && d > 6;
    let (a, b) = join(p, || batch(par, d - 1, i, nn, full, bound), || batch(par, d - 1, i + h, nn, full, bound));
    merge(a, b)
}

fn main() {
    let par = parallel();
    let s = batch(par, 17, 0, 17, 131071, 11730);
    println!("{}", s.sols.wrapping_mul(2654435761) ^ s.nodes);
}
