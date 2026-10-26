#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Vend {
    pub credit: i64,
    pub stock: i64,
    pub sold: i64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ev {
    Coin { v: i64 },
    Buy { price: i64 },
    Refund,
    Restock { n: i64 },
}

pub fn step(m: Vend, e: Ev) -> Vend {
    match e {
        Ev::Coin { v } => {
            if v > 0 && v <= 1_000_000 - m.credit {
                Vend { credit: m.credit + v, ..m }
            } else {
                m
            }
        }
        Ev::Buy { price } => {
            if price > 0 && m.stock > 0 && m.credit >= price && m.sold < 1_000_000_000 {
                Vend { credit: m.credit - price, stock: m.stock - 1, sold: m.sold + 1 }
            } else {
                m
            }
        }
        Ev::Refund => Vend { credit: 0, ..m },
        Ev::Restock { n } => {
            if n > 0 {
                let s = if n >= 100 - m.stock { 100 } else { m.stock + n };
                Vend { stock: s, ..m }
            } else {
                m
            }
        }
    }
}
