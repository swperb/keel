pub struct Vend { pub credit: i64, pub stock: i64, pub sold: i64 }
pub enum Ev { Coin { v: i64 }, Buy { price: i64 }, Refund, Restock { n: i64 } }

pub fn step(m: Vend, e: Ev) -> Vend {
    let mut m = m;
    match e {
        Ev::Coin { v } => {
            if v > 0 && v <= 1_000_000 - m.credit {
                m.credit += v;
            }
        }
        Ev::Buy { price } => {
            if price > 0 && m.stock > 0 && m.credit >= price && m.sold < 1_000_000_000 {
                m.credit -= price;
                m.stock -= 1;
                m.sold += 1;
            }
        }
        Ev::Refund => m.credit = 0,
        Ev::Restock { n } => {
            if n > 0 {
                m.stock = if n >= 100 - m.stock { 100 } else { m.stock + n };
            }
        }
    }
    m
}
