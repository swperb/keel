fn main() {
    println!("{}", first_index(&[], 5));
    println!("{}", first_index(&[7; 6], 7));
    let xs = [i64::MIN, -3, 4, 4, 4, 9, i64::MAX];
    for k in [4, 5, i64::MIN, i64::MAX, 10] {
        println!("{}", first_index(&xs, k));
    }
}
