fn show(m: Vend) {
    println!("{}", m.credit);
    println!("{}", m.stock);
    println!("{}", m.sold);
}
fn main() {
    show(step(Vend { credit: 0, stock: 0, sold: 0 }, Ev::Coin { v: 25 }));
    show(step(Vend { credit: 999990, stock: 5, sold: 0 }, Ev::Coin { v: 10 }));
    show(step(Vend { credit: 999990, stock: 5, sold: 0 }, Ev::Coin { v: 11 }));
    show(step(Vend { credit: 5, stock: 5, sold: 0 }, Ev::Coin { v: i64::MAX }));
    show(step(Vend { credit: 5, stock: 5, sold: 0 }, Ev::Coin { v: 0 }));
    show(step(Vend { credit: 5, stock: 5, sold: 0 }, Ev::Coin { v: i64::MIN }));
    show(step(Vend { credit: 100, stock: 3, sold: 7 }, Ev::Buy { price: 100 }));
    show(step(Vend { credit: 99, stock: 3, sold: 7 }, Ev::Buy { price: 100 }));
    show(step(Vend { credit: 100, stock: 0, sold: 7 }, Ev::Buy { price: 50 }));
    show(step(Vend { credit: 100, stock: 3, sold: 7 }, Ev::Buy { price: 0 }));
    show(step(Vend { credit: 100, stock: 3, sold: 7 }, Ev::Buy { price: i64::MIN }));
    show(step(Vend { credit: 100, stock: 3, sold: 1000000000 }, Ev::Buy { price: 1 }));
    show(step(Vend { credit: 1000000, stock: 100, sold: 0 }, Ev::Buy { price: 1000000 }));
    show(step(Vend { credit: 42, stock: 1, sold: 2 }, Ev::Refund));
    show(step(Vend { credit: 0, stock: 0, sold: 0 }, Ev::Refund));
    show(step(Vend { credit: 1, stock: 90, sold: 0 }, Ev::Restock { n: 10 }));
    show(step(Vend { credit: 1, stock: 90, sold: 0 }, Ev::Restock { n: 11 }));
    show(step(Vend { credit: 1, stock: 90, sold: 0 }, Ev::Restock { n: i64::MAX }));
    show(step(Vend { credit: 1, stock: 90, sold: 0 }, Ev::Restock { n: 0 }));
    show(step(Vend { credit: 1, stock: 90, sold: 0 }, Ev::Restock { n: i64::MIN }));
    show(step(Vend { credit: 1, stock: 100, sold: 0 }, Ev::Restock { n: 1 }));
}
