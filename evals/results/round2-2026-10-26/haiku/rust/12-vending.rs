#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Vend {
    pub credit: i64,
    pub stock: i64,
    pub sold: i64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ev {
    Coin { v: i64 },
    Buy { price: i64 },
    Refund,
    Restock { n: i64 },
}

pub fn step(m: Vend, e: Ev) -> Vend {
    let mut r = m;
    match e {
        Ev::Coin { v } => {
            // credit is in [0, 1_000_000], so the subtraction cannot overflow.
            if v > 0 && v <= 1_000_000 - m.credit {
                r.credit = m.credit + v;
            }
        }
        Ev::Buy { price } => {
            if price > 0 && m.stock > 0 && m.credit >= price && m.sold < 1_000_000_000 {
                r.credit = m.credit - price;
                r.stock = m.stock - 1;
                r.sold = m.sold + 1;
            }
        }
        Ev::Refund => {
            r.credit = 0;
        }
        Ev::Restock { n } => {
            if n > 0 {
                // stock is in [0, 100]; avoid overflow of stock + n.
                r.stock = if n >= 100 - m.stock { 100 } else { m.stock + n };
            }
        }
    }
    r
}
