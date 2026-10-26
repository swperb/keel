pub struct Vend { pub credit: i64, pub stock: i64, pub sold: i64 }
pub enum Ev { Coin { v: i64 }, Buy { price: i64 }, Refund, Restock { n: i64 } }

pub fn step(m: Vend, e: Ev) -> Vend {
    let Vend { credit, stock, sold } = m;
    match e {
        Ev::Coin { v } if v > 0 && v <= 1_000_000 - credit => Vend { credit: credit + v, stock, sold },
        Ev::Buy { price } if price > 0 && stock > 0 && credit >= price && sold < 1_000_000_000 => {
            Vend { credit: credit - price, stock: stock - 1, sold: sold + 1 }
        }
        Ev::Refund => Vend { credit: 0, stock, sold },
        Ev::Restock { n } if n > 0 => Vend { credit, stock: if n >= 100 - stock { 100 } else { stock + n }, sold },
        _ => Vend { credit, stock, sold },
    }
}
