fn main() {
    for (a, b) in [(12, 18), (0, 0), (0, 7), (7, 0), (i64::MAX, i64::MAX), (i64::MAX - 1, 6), (17, 5)] {
        println!("{}", gcd(a, b));
    }
}
