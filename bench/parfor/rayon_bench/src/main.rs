// The rayon side of bench/parfor: the same kernels as lcg.kl, triad.kl and
// logistic.kl, same arithmetic, same array sizes, same serial checksum. Run
// as `rayon_bench lcg|triad|logistic [serial]`; `serial` uses plain
// iterators instead.
use rayon::prelude::*;

fn mix(x0: i64, rounds: i64) -> i64 {
    let mut x = x0;
    for _ in 0..rounds {
        x = (x * 1103515245 + 12345) % 2147483648;
    }
    x
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let serial = args.get(2).map(|s| s == "serial").unwrap_or(false);
    match args.get(1).map(|s| s.as_str()) {
        Some("lcg") => {
            let mut out = vec![0i64; 10_000_000];
            let k = |(i, o): (usize, &mut i64)| *o = mix(i as i64, 256);
            if serial { out.iter_mut().enumerate().for_each(k) } else { out.par_iter_mut().enumerate().for_each(k) }
            println!("{}", out.iter().sum::<i64>());
        }
        Some("triad") => {
            let n = 50_000_000;
            let (mut xs, mut ys, mut zs) = (vec![0i64; n], vec![0i64; n], vec![0i64; n]);
            let fill = |v: &mut Vec<i64>, seed: i64| {
                let f = |(i, x): (usize, &mut i64)| *x = ((i as i64 * 7 + seed) % 2000) - 1000;
                if serial { v.iter_mut().enumerate().for_each(f) } else { v.par_iter_mut().enumerate().for_each(f) }
            };
            fill(&mut xs, 1);
            fill(&mut ys, 2);
            for _ in 0..21 {
                if serial {
                    zs.iter_mut().zip(&xs).zip(&ys).for_each(|((z, x), y)| *z = 3 * x + y);
                } else {
                    zs.par_iter_mut().zip(&xs).zip(&ys).for_each(|((z, x), y)| *z = 3 * x + y);
                }
            }
            println!("{}", zs.iter().sum::<i64>());
        }
        Some("logistic") => {
            let n = 10_000_000usize;
            let mut out = vec![0f32; n];
            let k = |(i, o): (usize, &mut f32)| {
                let mut x = (i as i64 + 1) as f32 / (n as i64 + 2) as f32;
                for _ in 0..256 {
                    x = (3.9f32 * x) * (1.0 - x);
                }
                *o = x;
            };
            if serial { out.iter_mut().enumerate().for_each(k) } else { out.par_iter_mut().enumerate().for_each(k) }
            // The same bit checksum as logistic.kl: h = (h * 31 + bits) mod 2^32.
            let h = out.iter().fold(0u32, |h, x| h.wrapping_mul(31).wrapping_add(x.to_bits()));
            println!("{}", h);
        }
        _ => {
            eprintln!("usage: rayon_bench lcg|triad|logistic [serial]");
            std::process::exit(2)
        }
    }
}
