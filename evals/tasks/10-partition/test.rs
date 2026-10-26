fn main() {
    let cases: Vec<(Vec<i64>, i64)> = vec![
        (vec![], 5),
        (vec![3, -1, 4, 1, -5, 9, 2, 6], 3),
        (vec![i64::MIN, i64::MAX, 0, i64::MIN, i64::MAX], 0),
        (vec![7, 7, 7], 7),
        (vec![1, 2, 3], i64::MIN),
        (vec![1, 2, 3], i64::MAX),
        (vec![5, 1, 5, 1, 5, 1], 2),
    ];
    for (mut xs, p) in cases {
        let r = partition(&mut xs, p);
        println!("{}", r);
        for x in &xs {
            println!("{}", x);
        }
    }
    let mut big = vec![1i64; 1_000_000];
    println!("{}", partition(&mut big, 2));
    println!("{}", big[999_999]);
}
