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
`a + (b * c)`. Chains of one associative operator are fine. Bitwise
operators follow the same rule: `a & b | c` and `a + b << 2` are errors. This removes an
entire class of misreadings, for models and people alike.

## Compared to Bend

Bend (bend-lang.com, v2.0.39 at the time of writing) describes itself as
having a proof-checking type checker in the style of Lean and Rocq, built on
an affine dependent type theory, near-C speed on one core, and automatic
parallelism across CPU cores and GPUs. We have not benchmarked Bend
ourselves, so this section only makes claims about Keel that we measured or
that the compiler enforces:

- **Explicit, statically race-free parallelism.** `par` branches run on free
  cores. Branches may share an array only through slices the verifier proves
  disjoint (`V-DISJOINT`), so divide and conquer over arrays needs no unsafe
  code or locks. The spawner forks only while a core is free.
- **Automated proofs with counterexamples.** Overflow, bounds, division by
  zero, contracts and termination are discharged by an SMT solver without
  hand-written proof terms; when a proof fails, the error carries concrete
  input values. Hand-written `lemma`s cover what the solver cannot find.
- **Anti-vacuity checks.** Contradictory preconditions (`V-VACUOUS`) and
  unreachable branches (`V-DEAD`) are errors, so a proof cannot pass by
  assuming the impossible.
- **Measured speed against Rust,** below. Keel compiles to check-free C, so
  single-core speed is C speed for the same algorithm.

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

Parallel mergesort of 10M integers (`examples/msort.kl`). The verifier
proves the output is sorted **and is a permutation of the input** (every
value occurs exactly as often as before), plus bounds, termination and race
freedom, in about 1 s:

```
par {
  msort(&mut xs[0..mid], &mut tmp[0..mid]);
  msort(&mut xs[mid..len(xs)], &mut tmp[mid..len(xs)]);
}
merge(&mut xs, &mut tmp, mid);
```

| same algorithm, 4096 cutoff | wall | CPU |
|---|---|---|
| Rust, `std::thread::scope` per split | 0.19 to 0.34 s | 1.2 s |
| Rust, `rayon::join` | 0.12 s | 0.75 s |
| Keel, `par` | 0.12 s | 0.72 s |

Keel matches rayon's work-stealing on the same algorithm and beats naive
threads. A better algorithm still wins: rayon's `par_sort_unstable` does it
in 0.04 s and single-threaded `sort_unstable` in 0.11 s. A tuned sort in
Keel's standard library is future work.

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
example verifies in 0.01 to 1 s.

Verification is deterministic: every check gets a fixed budget of solver
work (Z3's resource counter), never a wall-clock timeout, so the same file
gets the same verdict on every run and every machine load. Reachability
checks get a small budget, and any the solver cannot settle are reported as
inconclusive rather than silently passed. When a proof runs out of budget
in a function with a self-triggering quantifier such as
`forall t in 0..n { xs[t] < xs[t + 1] }`, the error names it and suggests
the pairwise form, which typically proves in under a second.

## The language

- Types: `i64`, `bool`, structs, enums with payloads, owned arrays `[i64]`, borrows `&[i64]` and `&mut [i64]`.
- Naming: types and variants start uppercase, values start lowercase (enforced; keeps the grammar unambiguous).
- Structs: `Point { x: 1, y: 2 }` lists every field in declaration order; `p.x = 3;` updates a `var`.
- Enums: always qualified, `Shape.Circle { r: 5 }`, `Shape.Empty`. `s is Shape.Circle` tests a variant. In specs, `(s as Shape.Circle).r` reads a payload.
- `match` is exhaustive with no wildcard, and arms follow declaration order: `Shape.Circle(c) => { ... c.r ... }`.
- Functions: `fn` is pure; `io fn` may print and call other `io fn`.
- Contracts: `requires`, `ensures` (with `result`), `decreases` (required for recursion).
- Ghost code: `spec fn` (single-expression math definitions, spec-only `if c { a } else { b }`), `lemma` (no loops; prove by cases, `assert` and recursion).
- Specs may also call an ordinary `fn` that is pure, loop-free and non-recursive, takes no `&mut`, and returns `i64`, `bool` or a struct/enum: write a helper like `tiles(mode)` once and use it in both code and contracts. Its body (`let`, `var`, `if`, `return`) is lifted to a definition.
- Statements: `let`, `var`, assignment, `xs[i] = v`, `if`/`else`, `while ... invariant ... decreases ...`, `return`, `assert`, `par`.
- Bitwise: `&`, `|`, `^`, `~`, `<<`, `>>` on `i64` (two's complement, as in C), and `0x`/`0b` literals. A shift amount must be proven in `0..64` (`V-SHIFT`), and `a << b` must fit in i64. `>>` is arithmetic (rounds toward negative infinity, unlike `/`). The verifier reads masks `x & (2^k - 1)` as `x mod 2^k` and other operators as 64-bit vector operations.
- Specs: `forall x in lo..hi { P }`, `forall v: i64 { P }` (every i64), `exists`, `==>`, `len(xs)`.
- Multisets: `count(&xs, lo, hi, v)` is the number of times `v` occurs in `xs[lo..hi]`; `old(e)` in `ensures`, invariants and asserts is `e` on function entry. Together they state permutations: `ensures forall v: i64 { count(&xs, 0, len(xs), v) == old(count(&xs, 0, len(xs), v)) }`.
- Slices: `&xs[lo..hi]` and `&mut xs[lo..hi]` borrow a range; the callee sees an array of length `hi - lo`. Two borrows of one array may coexist in a call or across `par` branches only if both are slices and the verifier proves the ranges disjoint.
- `par` branches are calls: `let x: i64 = f(..);` or, for unit functions, `f(..);`.
- Memory: arrays come from `array(n, fill)` or functions returning `[i64]`, are owned by one `let`, are borrowed only at call sites (so there are no lifetimes to annotate), and are freed when their scope ends unless returned.

## How verification works

`src/verify.rs` walks each function, tracking every variable as an SMT term
and a path condition. Loops are cut with their invariants: prove on entry,
havoc what the body modifies, assume the invariant, prove it is preserved and
that the measure decreases. Calls are modular: prove the callee's `requires`,
assume its `ensures` (and, for a pure loop-free `fn`, its lifted definition:
the verified body never overflows, so its mathematical reading is exact).
Each function's query holds only the `spec fn` definitions it reaches
through its own code and contracts and those of its callees, so adding a
definition elsewhere in a file cannot change whether an existing proof
passes. Integer semantics match C exactly (truncating division),
and because overflow is proven impossible, mathematical integers in the solver
equal machine integers in the binary. Each function's obligations go to its
own Z3 process, all in parallel. Any obligation the solver gives up on is
retried without quantified facts and array lambdas: dropping assumptions is
sound for proving, so an "unsat" there counts as proved, while a model found
there is reported as a counterexample marked possibly spurious, which is
still more useful to an agent than "solver gave up".

`count` is built in rather than a user `spec fn` because its useful facts
need induction to prove. Its definition unfolds a bounded number of times
(goals unfold twice, assumptions not at all, which keeps the solver out of
matching loops), and a few standard lemmas are axioms: splitting a range
adds counts, a single store changes at most one value's count, a slice
view counts like the matching range of its parent, and writing a slice
back only changes counts inside its range. These axioms are part of the
trusted base, alongside Z3 and the verifier.

## Status and roadmap

Working end-to-end compiler, no crates. `./tests/run.sh` runs the examples
and a suite of programs that must be rejected. Known limits: stack depth is
not yet bounded by the verifier; mutual recursion is rejected; recursive
types (lists, trees) are not supported yet; the trusted base is Z3, the
verifier and the C compiler (Lean's is a small proof kernel). If you can get
a bad program past `keel check`, see [BREAK_IT.md](BREAK_IT.md).

Next, roughly in order:
1. Sized integers (`u8`..`u64`, `i32`), arrays of any element type, recursive types.
2. A tuned standard library sort with the same sortedness and permutation guarantees, and faster failure on false multiset claims (today a wrong permutation claim is rejected only after the solver times out, about 13 s).
3. `old(...)` in ensures, and cross-checking proofs with a second solver (cvc5) to shrink the trusted base.
4. `keel fmt` as the single canonical layout, and a proof cache keyed by function hash for fast agent iteration.
5. Proven stack bounds, arena regions, and an LLVM backend.

## License

The compiler is AGPL-3.0 with an output exception: programs you write in
Keel, and everything the compiler generates from them, are yours under any
license. Commercial licenses for the compiler are available. See
[LICENSING.md](LICENSING.md) and [CONTRIBUTING.md](CONTRIBUTING.md).
