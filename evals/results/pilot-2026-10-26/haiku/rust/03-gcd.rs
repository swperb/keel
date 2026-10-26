pub fn gcd(a: i64, b: i64) -> i64 {
    // Euclid's algorithm on non-negative values; gcd(0, 0) = 0 falls out naturally.
    let mut a = a;
    let mut b = b;
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}
