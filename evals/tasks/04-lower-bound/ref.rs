pub fn first_index(xs: &[i64], key: i64) -> i64 {
    let i = xs.partition_point(|&x| x < key);
    if i < xs.len() && xs[i] == key { i as i64 } else { -1 }
}
