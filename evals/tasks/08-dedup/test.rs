fn show(xs: &[i64], n: usize) {
    println!("{}", n);
    for x in &xs[..n] {
        println!("{}", x);
    }
}
fn main() {
    let cases: Vec<Vec<i64>> = vec![
        vec![],
        vec![i64::MIN],
        vec![7; 1_000_000],
        vec![i64::MIN, i64::MIN, -5, 0, 0, 0, 3, i64::MAX, i64::MAX],
        vec![1, 2, 3, 4],
        vec![1, 2, 2],
    ];
    for mut c in cases {
        let n = dedup(&mut c);
        show(&c, n);
    }
}
