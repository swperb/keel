#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Op {
    Add { a: i64, b: i64 },
    Div { a: i64, b: i64 },
    Neg { a: i64 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Res {
    Ok { v: i64 },
    Err,
}

pub fn eval(op: Op) -> Res {
    let r = match op {
        Op::Add { a, b } => a.checked_add(b),
        Op::Div { a, b } => {
            if b == 0 {
                None
            } else {
                // checked_div also rejects i64::MIN / -1 (overflow).
                a.checked_div(b)
            }
        }
        Op::Neg { a } => a.checked_neg(),
    };
    match r {
        Some(v) => Res::Ok { v },
        None => Res::Err,
    }
}
