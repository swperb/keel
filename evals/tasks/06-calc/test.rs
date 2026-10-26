fn show(r: Res) { match r { Res::Ok { v } => println!("{}", v), Res::Err => println!("-424242") } }
fn main() {
    show(eval(Op::Add { a: 2, b: 3 }));
    show(eval(Op::Add { a: i64::MAX, b: 1 }));
    show(eval(Op::Add { a: i64::MIN, b: -1 }));
    show(eval(Op::Add { a: i64::MAX, b: i64::MIN }));
    show(eval(Op::Div { a: 7, b: -2 }));
    show(eval(Op::Div { a: 5, b: 0 }));
    show(eval(Op::Div { a: i64::MIN, b: -1 }));
    show(eval(Op::Neg { a: i64::MIN }));
    show(eval(Op::Neg { a: i64::MAX }));
}
