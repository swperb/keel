# Keel

A systems language built for agents first. If a program compiles, it has been
**proven** free of integer overflow, out-of-bounds access, division by zero,
contract violations, data races and non-termination. Because every safety
property is proven up front, the generated code has no runtime checks at all.

```
fn search(xs: &[i64], key: i64) -> i64
  requires forall i in 0..len(xs) { forall j in i..len(xs) { xs[i] <= xs[j] } }
  ensures result == -1 || (0 <= result && result < len(xs) && xs[result] == key)
  ensures result == -1 ==> forall k in 0..len(xs) { xs[k] != key }
{
  var lo: i64 = 0;
  var hi: i64 = len(xs);
  while lo < hi
    invariant 0 <= lo && lo <= hi && hi <= len(xs)
    invariant forall k in 0..lo { xs[k] < key }
    invariant forall k in hi..len(xs) { xs[k] > key }
    decreases hi - lo
  {
    let mid: i64 = lo + ((hi - lo) / 2);
    ...
```

## Why agents

Humans want terse syntax and flexibility. Agents want the opposite: one
obvious way to write each thing, local reasoning, and a compiler that says
exactly what is wrong. Keel is designed around that.

| Goal | How Keel gets there |
|---|---|
| Strictest verification | Every function is symbolically executed and each risky operation becomes an SMT proof obligation (Z3). Unproven means rejected. There is no `assume`, no `unsafe`, no escape hatch. |
| Rust speed | Compiles to C11 at `-O3`. No GC, no runtime checks, `&mut` borrows lower to `restrict` pointers. Benchmarks match hand-written Rust. |
| Go-sized design space | One loop (`while`, which must state a `decreases` measure), one conditional, no ternary, no shadowing, no operator precedence, no overloading, no implicit conversions, no macros, no exceptions, no null, no globals. |
| Economical | Zero-dependency compiler. Tiny runtime (alloc + a core-bounded spawner). Memory freed deterministically at scope exit. No warmup, no heap tuning: the program is as fast on a small box as it will ever be per core. |
| Agent feedback | Stable error codes, `--json` output, and **concrete counterexamples** from the solver (`a = -1, b = -9223372036854775808`). `keel explain CODE` gives the long form. |

### No precedence, on purpose

`a + b * c` is a compile error (E-PAREN). So is `a && b || c`. You write
`a + (b * c)`. Chains of one associative operator are fine. This removes an
entire class of misreadings, for models and people alike.

## Compared to Bend

Bend parallelizes everything implicitly via interaction nets, which is
beautiful but slow per core and dynamically typed. Keel takes the opposite
trade: parallelism is explicit (`par`), but it is **statically race-free**
(an `&mut` borrow in one branch may not appear in another) and runs at native
C speed. The spawner only forks while a core is free, so recursion does not
explode into thousands of threads.

```
par {
  let a: i64 = count_primes(lo, mid);
  let b: i64 = count_primes(mid, hi);
}
return a + b;
```

On a 15-core M-series Mac, counting primes below 20M (`examples/primes.kl`):

| | wall | CPU |
|---|---|---|
| Rust, serial | 2.72 s | 2.50 s |
| Rust, scoped threads | 0.20 s | 2.87 s |
| Keel, `par` | 0.23 s | 2.85 s |

## Usage

```
cargo build --release
./target/release/keel check examples/search.kl       # prove
./target/release/keel run examples/primes.kl         # prove, compile, run
./target/release/keel build examples/sum.kl -o sum --emit-c
./target/release/keel check examples/bad.kl --json   # machine-readable failures
./target/release/keel explain V-OVERFLOW
./tests/run.sh                                       # full test suite
```

Requires `z3` on PATH (or `KEEL_Z3`) and a C compiler (`CC`, default `cc`).

## Proofs, not just checks

When the solver cannot find a proof on its own, you write one, Lean style.
`spec fn` defines mathematics, `lemma` proves facts about it (a recursive
lemma is a proof by induction), and code invokes lemmas to justify itself.
Both are erased before codegen (`examples/proofs.kl`):

```
spec fn total(xs: &[i64], n: i64) -> i64
  requires 0 <= n && n <= len(xs)
  decreases n
{
  if n == 0 { 0 } else { total(&xs, n - 1) + xs[n - 1] }
}

lemma total_bounds(xs: &[i64], n: i64)
  requires 0 <= n && n <= len(xs)
  requires forall k in 0..len(xs) { 0 <= xs[k] && xs[k] <= 1000 }
  ensures 0 <= total(&xs, n) && total(&xs, n) <= 1000 * n
  decreases n
{
  if n > 0 {
    total_bounds(&xs, n - 1);
  }
}
```

### Proofs that cannot cheat

A verifier only proves code matches its spec, so the classic way to get a
"proof" through is to weaken the problem. Keel rejects the common tricks
(`examples/cheat.kl`):

| Trick | Result |
|---|---|
| Contradictory `requires` (everything follows from false) | `V-VACUOUS` |
| A branch or loop body that can never run | `V-DEAD` |
| An invariant that contradicts the loop | `V-INVARIANT-ENTRY` / `V-DEAD` |
| A `spec fn` that is circular (would make the logic inconsistent) | `V-TERMINATION`, checked before any definition is trusted |
| `assume`, `unsafe`, `admit`, `sorry` | Do not exist |

What no tool can catch is a spec that faithfully says the wrong thing. Keel
narrows that gap (specs are short, explicit and checked for vacuity) but
reviewing the `requires`/`ensures` lines remains the human's job, and it is
a much smaller job than reviewing the code.

### Speed

Each function's obligations go to their own Z3 process in parallel. Every
example verifies in 0.01 to 0.6 s. Reachability checks get a 300 ms budget
and any the solver cannot settle are reported as inconclusive rather than
silently passed.

## The language

- Types: `i64`, `bool`, structs, enums with payloads, owned arrays `[i64]`, borrows `&[i64]` and `&mut [i64]`.
- Naming: types and variants start uppercase, values start lowercase (enforced; keeps the grammar unambiguous).
- Structs: `Point { x: 1, y: 2 }` lists every field in declaration order; `p.x = 3;` updates a `var`.
- Enums: always qualified, `Shape.Circle { r: 5 }`, `Shape.Empty`. `s is Shape.Circle` tests a variant. In specs, `(s as Shape.Circle).r` reads a payload.
- `match` is exhaustive with no wildcard, and arms follow declaration order: `Shape.Circle(c) => { ... c.r ... }`.
- Functions: `fn` is pure; `io fn` may print and call other `io fn`.
- Contracts: `requires`, `ensures` (with `result`), `decreases` (required for recursion).
- Ghost code: `spec fn` (single-expression math definitions, spec-only `if c { a } else { b }`), `lemma` (no loops; prove by cases, `assert` and recursion).
- Statements: `let`, `var`, assignment, `xs[i] = v`, `if`/`else`, `while ... invariant ... decreases ...`, `return`, `assert`, `par`.
- Specs: `forall x in lo..hi { P }`, `exists`, `==>`, `len(xs)`.
- Memory: arrays come from `array(n, fill)` or functions returning `[i64]`, are owned by one `let`, are borrowed only at call sites (so there are no lifetimes to annotate), and are freed when their scope ends unless returned.

## How verification works

`src/verify.rs` walks each function, tracking every variable as an SMT term
and a path condition. Loops are cut with their invariants: prove on entry,
havoc what the body modifies, assume the invariant, prove it is preserved and
that the measure decreases. Calls are modular: prove the callee's `requires`,
assume its `ensures`. Integer semantics match C exactly (truncating division),
and because overflow is proven impossible, mathematical integers in the solver
equal machine integers in the binary. Each function's obligations go to its
own Z3 process, all in parallel.

## Status and roadmap

Working end-to-end compiler, no crates. `./tests/run.sh` runs the examples
and a suite of programs that must be rejected. Known limits: stack depth is
not yet bounded by the verifier; mutual recursion is rejected; recursive
types (lists, trees) are not supported yet; the trusted base is Z3, the
verifier and the C compiler (Lean's is a small proof kernel).

Next, roughly in order:
1. Sized integers (`u8`..`u64`, `i32`), arrays of any element type, recursive types.
2. Disjoint `&mut` slices (`split(&mut xs, mid)`) so `par` covers array divide and conquer (parallel mergesort).
3. `old(...)` in ensures, and cross-checking proofs with a second solver (cvc5) to shrink the trusted base.
4. `keel fmt` as the single canonical layout, and a proof cache keyed by function hash for fast agent iteration.
5. Proven stack bounds, arena regions, and an LLVM backend.

## License

The compiler is AGPL-3.0 with an output exception: programs you write in
Keel, and everything the compiler generates from them, are yours under any
license. Commercial licenses for the compiler are available. See
[LICENSING.md](LICENSING.md) and [CONTRIBUTING.md](CONTRIBUTING.md).
