fn main() {
    for (a, b) in [(3, 4), (-3, -4), (-1, 0), (i64::MAX, i64::MAX), (i64::MIN, i64::MIN), (i64::MIN, i64::MAX), (i64::MAX, i64::MAX - 1), (-7, 2)] {
        println!("{}", midpoint(a, b));
    }
}
