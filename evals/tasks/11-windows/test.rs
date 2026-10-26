fn main() {
    let xs = vec![3, -1, -1_000_000_000, 4, 1_000_000_000, -2];
    let mut pre = vec![-1i64; 7];
    prefix(&xs, &mut pre);
    for p in &pre {
        println!("{}", p);
    }
    println!("{}", range_sum(&xs, &pre, 0, 6));
    println!("{}", range_sum(&xs, &pre, 2, 2));
    println!("{}", range_sum(&xs, &pre, 1, 4));
    for w in [1, 2, 6, 0, 7, i64::MIN] {
        println!("{}", best_window(&xs, w));
    }
    println!("{}", best_window(&[], 0));
    println!("{}", best_window(&[], 1));
    println!("{}", best_window(&[-1_000_000_000; 5], 2));
    let big = vec![1_000_000_000i64; 1_000_000];
    println!("{}", best_window(&big, 1_000_000));
    println!("{}", best_window(&big, 999_999));
}
