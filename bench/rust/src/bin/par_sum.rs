// Bend's demos/pure_par_sum at d = 30: the sum of 0 .. 2^30 as a fork/join
// tree down to single numbers, forking above 2^16 numbers (as in Keel).
use keel_bench_rust::{join, parallel};

fn sum(par: bool, i: i64, n: i64) -> i64 {
    if n == 1 {
        return i;
    }
    let h = n / 2;
    if n <= 65536 {
        return sum(false, i, h) + sum(false, i + h, n - h);
    }
    let (a, b) = join(par, || sum(par, i, h), || sum(par, i + h, n - h));
    a + b
}

fn main() {
    let par = parallel();
    let s = sum(par, 0, 1 << 30);
    println!("{}", s);
    println!("{}", s as u32);
}
