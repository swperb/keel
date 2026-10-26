fn show(xs: &[i64]) {
    for x in xs {
        println!("{}", x);
    }
}
fn main() {
    let mut e: Vec<i64> = vec![];
    rotate(&mut e, 3);
    show(&e);
    println!("-1");
    for k in [2, -1, i64::MIN, i64::MAX, 10] {
        let mut a = vec![1, 2, 3, 4, 5];
        rotate(&mut a, k);
        show(&a);
        println!("-1");
    }
    let mut g = vec![42];
    rotate(&mut g, 7);
    show(&g);
    println!("-1");
    let mut h = vec![0i64; 1_000_000];
    rotate(&mut h, 999_999);
    println!("{}", h[0]);
}
