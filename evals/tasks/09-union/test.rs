fn main() {
    let a = vec![i64::MIN, 1, 1, 4, i64::MAX];
    let b = vec![0, 1, 4, 4, 5, i64::MAX];
    let big = vec![3i64; 1_000_000];
    let cases: Vec<(Vec<i64>, Vec<i64>)> = vec![
        (vec![], vec![]),
        (a.clone(), vec![]),
        (vec![], a.clone()),
        (a.clone(), b.clone()),
        (big.clone(), big.clone()),
        (vec![10, 20, 30], vec![1, 2, 3]),
    ];
    for (x, y) in cases {
        let mut out = vec![0i64; x.len() + y.len()];
        let n = union(&x, &y, &mut out);
        println!("{}", n);
        for v in &out[..n] {
            println!("{}", v);
        }
    }
}
