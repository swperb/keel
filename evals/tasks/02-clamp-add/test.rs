fn main() {
    for (a, b, lo, hi) in [(2, 3, 0, 10), (i64::MAX, 1, 0, 100), (i64::MIN, -1, -50, 50), (i64::MAX, i64::MIN, -5, 5), (i64::MIN, i64::MAX, i64::MIN, i64::MIN), (5, 5, 10, 10), (-20, 3, -10, 10)] {
        println!("{}", clamp_add(a, b, lo, hi));
    }
}
