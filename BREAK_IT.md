# Break Keel

Keel makes one promise: if `keel check` passes, the program cannot overflow,
index out of bounds, divide by zero, race, loop forever, or violate its own
contracts. The compiled C has no runtime checks, so if the verifier is wrong,
nothing catches it. A program that gets through when it should not is a
soundness bug, and it is the most valuable thing you can find.

This page says what counts, where we think the weak spots are, and how to
report what you find.

## What counts

A soundness bug is a program that `keel check` accepts and that, at run
time, does one of these:

- overflows `i64` (any `+`, `-`, `*`, `/`, `%` or negation)
- reads or writes an array out of bounds, or slices out of range
- divides or takes a remainder by zero
- has a data race between `par` branches
- runs forever (a loop or recursion that does not terminate)
- returns a value, or leaves an array, that violates its `ensures`, or
  reaches a point where a proven `assert` is false

Also in scope: a vacuous proof that slips past the anti-cheat checks. That
is a function whose `requires` contradict each other, or a branch or loop
body that can never run, that is accepted without `V-VACUOUS` or `V-DEAD`.
Reachability checks the solver cannot settle are printed as a note
("reachability check(s) inconclusive") rather than failing the build; a
contradiction hidden that way counts if the proof that relies on it is
accepted.

The runtime evidence does not have to be a crash. `keel check` proving
`assert x == 7` while `keel run` prints `x` as 0 is enough.

## What does not count

- **A spec that says the wrong thing.** Keel proves the code meets its
  `requires` and `ensures`. If those lines do not say what you meant, the
  proof is still correct. Weak specs are a design topic, not a soundness bug.
- **Solver budget exhaustion.** `V-UNKNOWN` on a correct program means the
  verifier is incomplete, not unsound. Those are welcome as ordinary issues.
- **Stack depth.** Recursion depth is not bounded by the verifier yet. A
  stack overflow from deep recursion is a documented limit.
- **Running out of memory.** `array(n, fill)` is proven to have
  `0 <= n <= 2^40`; whether the machine has that much memory is not
  checked.
- **Compiler crashes and rejected C.** A `keel` panic, or `keel run` failing
  with "C compiler failed", is a bug, but the program never ran. Report it as
  an ordinary issue. If the C compiles and misbehaves, it is soundness.
- **Bugs in Z3 or the C compiler.** They are part of the trusted base. Tell
  us anyway, since we may be able to avoid the construct that triggers them.

## Where to look

The verifier is small. `src/check.rs` (names, types, borrows, effects) runs
first, then `src/verify.rs` symbolically executes each function and turns
every risky operation into a Z3 query. These are the parts we trust least.

### Slice write-back

A call with `&mut xs[lo..hi]` hands the callee a view, `(lambda (i) (select
xs (+ i lo)))`, of length `hi - lo`. After the call, the caller's array
becomes a fresh lambda that reads the callee's final array in `[lo, hi)` and
the old array everywhere else. Ideas:

- Two `&mut` slices of one array in the same call; the write-backs are
  applied one after the other.
- A callee that reslices its own slice parameter and passes it on.
- Empty slices, `lo == hi`, slices at `len(xs)`.
- Slices inside loops, where the array is havocked and only the invariant
  survives.

### `par` disjointness

Each branch is a single call. `src/check.rs` rejects an exclusive borrow
next to any other use of the same array, unless both are slices; the
verifier then proves slice ranges disjoint (`V-DISJOINT`). Branches are
verified one after another, while at run time every branch's arguments are
evaluated first and the calls then run concurrently. Ideas:

- Anything a later branch's arguments can observe about an earlier branch's
  effects. (This is how the first bug below was found.)
- Borrows hidden inside nested calls in branch arguments.
- A function that receives two `&mut` parameters and runs `par` on them.

### Spec fn axioms and two-phase checking

A `spec fn` becomes an SMT function with the axiom `requires ==> f(args) ==
body`, quantified over its parameters with the call as the trigger. Phase 1
checks every definition's well-formedness and termination with no axioms at
all; only then does phase 2 check code and lemmas with the axioms. An
inconsistent axiom set would prove anything, so:

- Try to get a circular or non-terminating definition through phase 1, for
  example through calls inside quantifiers or `if` expressions, through
  `decreases` measures that use other spec fns, or through `requires` that
  mention spec fns.
- A spec fn applied to a slice sees a lambda view, not the array. Look for
  facts that hold for one representation and not the other.

### Lemma ghost arithmetic

Inside a lemma, integers are mathematical: no `i64` bounds on parameters or
locals, and no bounds or overflow checks on its arithmetic. Lemma arguments
at the call site are spec expressions too. The lemma's `ensures` become
facts in the calling code. Look for a way to make a lemma conclude something
about a mathematical value that the calling code then mistakes for a machine
value, or about an array element outside `0..len`.

### Match and datatype encoding

Structs and enums are SMT datatypes. Payload accessors applied to the wrong
variant are unspecified values, and `i64` range facts are asserted for every
field of every variant. `as` reads a payload in specs without a variant
check. Try nested enums inside structs, field assignment through paths
(`p.a.b = v`), and `match` arms whose bodies return.

### Division semantics

Division and remainder are modeled by `cdiv`/`cmod`, which truncate toward
zero like C. `i64::MIN / -1` and `i64::MIN % -1` are rejected as overflow.
Inside specifications, division by zero is not checked; the solver treats
`x / 0` as some unknown value. Try mixed signs, negative divisors, and
specs whose meaning depends on what `x / 0` is.

### The quantifier-free retry

When the solver gives up on an obligation, it is retried with every fact
containing `forall`, `exists` or `lambda` dropped, and with no spec fn
axioms. Dropping assumptions can only make a proof harder, so an `unsat`
there is trusted. The weak spot is the script construction, not the logic:
`is_quantified` matches by text, and results are matched to obligations by
`(echo "@N")` markers. Any way to make an answer land on the wrong
obligation is a soundness bug.

### Evaluation order and code generation

The verifier evaluates left to right. C does not promise an order for
operands, arguments or initializer lists, which is why a call that takes
`&mut` must be a whole statement or initializer. Look for any other place
where the C in `src/codegen.rs` (see it with `keel build --emit-c`) does
something the verifier did not model: scope-exit frees, struct copies, the
`par` thunks, `-O3` exploiting undefined behavior.

### Anti-vacuity

`V-VACUOUS` and `V-DEAD` are reachability checks: the path condition must be
satisfiable. They get a small fixed solver budget, and an inconclusive answer is
reported but does not fail the build. A vacuous proof that passes quietly is
in scope.

### Names

Your identifiers become SMT symbols (`v.name.N`, `sf.name`, `Type.field`,
`Enum.Variant`). The verifier now fails a function if Z3 rejects any line of
its script, but collisions that Z3 accepts with a different meaning would
not be caught that way.

## How to report

Open a [soundness report](https://github.com/swperb/keel/issues/new?template=soundness.yml).
It asks for:

1. **A minimal `.kl` file.** Cut it down until removing anything makes the
   problem go away. Fewer than 30 lines is ideal.
2. **The `keel check` output,** showing it was accepted (the "obligations
   proved" line, or `--json`).
3. **Runtime evidence:** the `keel run` output, or the emitted C
   (`keel build file.kl -o prog --emit-c`) with a sentence on what goes
   wrong. Say what you expected the verifier to reject and why.
4. **Versions:** `git rev-parse HEAD`, `z3 --version`, `cc --version`, and
   the OS.

Every accepted soundness fix ships with your program, or a reduction of it,
as a test in `tests/reject/` that failed before the fix. It stays there so
the bug cannot come back.

## Hall of fame

People who found soundness bugs in Keel. Thank you.

| Reporter | Bug | Test |
|---|---|---|
| | | |

## Found before launch

Bugs we found ourselves while writing this page, as examples of what counts.
Each has a test in `tests/reject/`.

| Bug | Evidence | Test |
|---|---|---|
| `par` branch arguments read an array another branch writes; the verifier saw the write first, the program did not | proved `x == 7`, printed `0` | `par_arg_read.kl` |
| `a[i] = f(&mut a)` stored into the array as it was before the call, losing the call's writes | proved `a[1] == 0`, printed `7` | `store_mut_call.kl` |
| A `&mut` call nested inside a larger expression; C may evaluate its neighbours first | accepted; correct on clang, order unspecified in C | `nested_mut_call.kl` |
| An owned `[i64]` parameter accepted `&a` and let the callee write through it | accepted; codegen then failed | `owned_array_param.kl` |
| A type named `Int` collided with the solver's `Int` sort, and Z3 dropped the facts that used it without the verifier noticing | accepted with missing facts | `reserved_type_name.kl` |
| A spec fn calling itself in its own `requires` crashed the verifier | stack overflow in `keel` | `spec_self_requires.kl` |
