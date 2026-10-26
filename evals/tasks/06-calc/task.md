# eval (enums)

Define exactly these types (Keel syntax first, then Rust):

```
enum Op { Add { a: i64, b: i64 }, Div { a: i64, b: i64 }, Neg { a: i64 } }
enum Res { Ok { v: i64 }, Err }
```
```rust
pub enum Op { Add { a: i64, b: i64 }, Div { a: i64, b: i64 }, Neg { a: i64 } }
pub enum Res { Ok { v: i64 }, Err }
```

`eval(op)` returns `Res.Ok` with the 64-bit result, or `Res.Err` when the
mathematically exact result does not fit in i64 or when dividing by zero.
`Div` truncates toward zero (like C and Rust `/`). Must be correct for every
input.

Keel signature: `fn eval(op: Op) -> Res`
Rust signature: `pub fn eval(op: Op) -> Res`
