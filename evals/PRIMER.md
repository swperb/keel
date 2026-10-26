# Keel in one page

Keel is a small language where every program is **proven** correct by an SMT
solver before it compiles: no integer overflow, no out-of-bounds access, no
division by zero, every `requires`/`ensures` holds, every loop and recursion
terminates. If `keel check file.kl` succeeds, those facts are machine-checked.

## Types and values
- Integers `i64`, `i32`, `i16`, `i8`, `u32`, `u16`, `u8`, and `bool`. No floats, no
  strings, no `u64`. Arithmetic is done in i64; storing into a narrower type
  (let, assignment, array element, field, argument, return) must be proven to
  fit. `wrap_u32(e)` etc. reduce modulo 2^N when wrapping is wanted.
- Arrays of any integer type: `[u8]`, `&[u16]`, `&mut [u32]`; `array(n, fill)`
  takes its element type from the `let` it is bound to.
- Bitwise operators `& | ^ ~ << >>` work on `i64` as in C, with `0xFF` and
  `0b1010` literals. Shift amounts must be proven in `0..64`; `>>` rounds
  down (`-5 >> 1 == -3`), unlike `/`. Mixing them with other operators needs
  parentheses: `(w >> 4) & 0xF`.
- Arrays: owned `[i64]`, shared borrow `&[i64]`, exclusive borrow `&mut [i64]`.
  Create with `array(len, fill)`. Read `xs[i]`, write `xs[i] = v;`, length `len(xs)`.
  Pass to functions as `&xs` or `&mut xs` (always written at the call site).
- Structs: `struct Point { x: i64, y: i64 }`, literal `Point { x: 1, y: 2 }`
  (all fields, declaration order), access `p.x`, update `p.x = 3;` (p must be `var`).
- Enums: `enum Shape { Circle { r: i64 }, Empty }`, values `Shape.Circle { r: 5 }`, `Shape.Empty`.
  Test with `s is Shape.Circle`. Branch with `match` (below).
- Type and variant names start Uppercase; variables, fields and functions start lowercase.

## Functions and statements
```
fn name(a: i64, xs: &[i64]) -> i64
  requires <bool expr>        // precondition (any number)
  ensures <bool expr>         // postcondition; `result` is the return value
  decreases <i64 expr>        // required if the function calls itself
{
  let x: i64 = 1;             // immutable
  var y: i64 = 2;             // mutable
  y = y + x;
  if y > 2 { ... } else if y < 0 { ... } else { ... }
  while y < 10
    invariant 0 <= y && y <= 10     // any number of invariants
    decreases 10 - y                // required on every loop
  {
    y = y + 1;
  }
  assert y == 10;             // proven, then erased
  match s {                   // every variant, in declaration order, no wildcard
    Shape.Circle(c) => { return c.r; }   // binder for a variant with fields
    Shape.Empty => { return 0; }         // no binder when there are no fields
  }
  return y;
}
```
- Every path of a non-unit function must end in `return`. No statements after `return`.
- Local names may not shadow names still in scope.
- `io fn main()` is the entry point; only `io fn` may call `print(i64)`.

## Operators: no precedence
`+ - * / %`, `== != < <= > >=`, `&& || !`, and `==>` (implies, specs only).
Different operators never mix without parentheses: `a + b * c` is an error,
write `a + (b * c)`. `a && b || c` is an error. Chains of one operator are fine
(`a + b - c`, `a && b && c`). Comparisons do not chain: write `a <= b && b < c`.
`/` and `%` truncate toward zero, like C. Literal range: -9223372036854775808..=9223372036854775807.

## Specifications
- Inside `requires`, `ensures`, `invariant`, `decreases`, `assert`, arithmetic is
  **mathematical** (unbounded): `a + b` there never overflows, so you can state
  facts about exact sums.
- Quantifiers: `forall k in lo..hi { P }` and `exists k in lo..hi { P }` (hi exclusive).
- In code, every arithmetic op must be proven in range. Typical fixes: add a
  `requires` bound, add a loop `invariant`, or test before computing
  (`if a > 9223372036854775807 - b { ... }` guards `a + b` when `b >= 0`).
- `(s as Shape.Circle).r` reads a payload in specs; in code use `match`.
- `spec fn f(..) -> i64 { <expr> }` defines math usable only in specs; its body
  is one expression and may use `if c { a } else { b }`.
- Specs may also call a plain `fn` that has no loops, no recursion and no
  `&mut` parameters (for example `ensures result == tiles(mode) * 512`); no
  duplicate `spec fn` is needed for such helpers.
- `lemma l(..) requires .. ensures .. { .. }` proves a fact; call it as a
  statement `l(args);` to use the fact. Recursive lemmas are induction.

## The verifier's errors
`keel check file.kl` prints errors like
`file.kl:3:13: error[V-OVERFLOW]: '+' may overflow i64` followed by a concrete
`counterexample: a = 9223372036854775807, b = 1` and a hint. Common codes:
V-OVERFLOW, V-BOUNDS, V-DIVZERO, V-REQUIRES (a call's precondition), V-ENSURES,
V-INVARIANT-ENTRY / V-INVARIANT-KEPT, V-TERMINATION, V-VACUOUS (contradictory
requires), V-DEAD (a branch that can never run), E-PAREN (add parentheses).
`keel explain CODE` describes any code. Proofs about loops almost always need
invariants that bound every variable the body changes.
State ordering facts pairwise, `forall a in lo..hi { forall b in a..hi { xs[a] <= xs[b] } }`,
not as neighbors (`xs[t] <= xs[t + 1]`): the neighbor form can make the solver
loop until it runs out of budget.

## Complete example
```
fn sum(xs: &[i64]) -> i64
  requires len(xs) <= 1_000_000
  requires forall k in 0..len(xs) { 0 <= xs[k] && xs[k] <= 1000 }
  ensures result >= 0
{
  var s: i64 = 0;
  var i: i64 = 0;
  while i < len(xs)
    invariant 0 <= i && i <= len(xs)
    invariant 0 <= s && s <= i * 1000
    decreases len(xs) - i
  {
    s = s + xs[i];
    i = i + 1;
  }
  return s;
}
```
