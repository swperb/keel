# vending machine (struct + enum state machine)

Define exactly these types (Keel syntax first, then Rust):

```
struct Vend { credit: i64, stock: i64, sold: i64 }
enum Ev { Coin { v: i64 }, Buy { price: i64 }, Refund, Restock { n: i64 } }
```
```rust
pub struct Vend { pub credit: i64, pub stock: i64, pub sold: i64 }
pub enum Ev { Coin { v: i64 }, Buy { price: i64 }, Refund, Restock { n: i64 } }
```

`step(m, e)` returns the machine state after event `e`. The input state
always satisfies `0 <= credit <= 1_000_000`, `0 <= stock <= 100` and
`0 <= sold <= 1_000_000_000`; the payloads `v`, `price` and `n` may be any
i64. Fields not mentioned in a rule are unchanged; a rejected event leaves
the whole state unchanged.

- `Coin { v }`: accepted when `v > 0` and the new credit `credit + v` would be
  at most 1_000_000; then `credit` increases by `v`. Otherwise rejected.
- `Buy { price }`: accepted when `price > 0`, `stock > 0`,
  `credit >= price` and `sold < 1_000_000_000`; then `credit` decreases by
  `price`, `stock` decreases by 1 and `sold` increases by 1. Otherwise
  rejected.
- `Refund`: `credit` becomes 0.
- `Restock { n }`: when `n > 0`, `stock` becomes `stock + n`, capped at 100.
  When `n <= 0`, rejected.

Keel signature: `fn step(m: Vend, e: Ev) -> Vend`
Rust signature: `pub fn step(m: Vend, e: Ev) -> Vend`
