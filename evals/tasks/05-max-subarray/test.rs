fn main() {
    println!("{}", max_subarray(&[]));
    println!("{}", max_subarray(&[-1_000_000; 5]));
    println!("{}", max_subarray(&vec![1_000_000; 1_000_000]));
    println!("{}", max_subarray(&[-2, 1, -3, 4, -1, 2, 1, -5]));
}
