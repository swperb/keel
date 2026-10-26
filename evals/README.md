# Keel evals

Does a verified language make agents produce more correct code, and more
*knowably* correct code, than a mainstream one? These evals hand the same
natural-language tasks to models of different strength, once in Keel and
once in Rust, and score the results against hidden tests.

## Method

- **Tasks** (`tasks/*/task.md`): six short specs chosen for the bugs agents
  actually make: overflow at extreme values (`midpoint`, `clamp_add`, `calc`),
  off-by-one and duplicates (`first_index`), floor vs truncation
  (`midpoint`), empty and all-negative inputs (`max_subarray`), zero cases
  (`gcd`), and enums (`calc`).
- **Agents** get only the task statements (and, for Keel, the one-page
  `PRIMER.md`; no model has seen Keel before). They write one file per task
  with no `main`, and may run their toolchain at most 5 times per task,
  including their own ad hoc tests. Prompt: `AGENT_PROMPT.md`.
- **Hidden harness** (`tasks/*/test.{kl,rs}`, `expected.txt`): appends a
  `main` that calls the solution on edge-case inputs. Rust is compiled with
  overflow checks on, so overflow is a crash rather than a silently wrong
  answer. For Keel the harness itself must verify, so a solution whose
  `requires` excludes valid inputs is caught (`harness_reject`).
- **Reference solutions** (`tasks/*/ref.*`) must pass:
  `python3 evals/score.py --ref`.

Round 2 adds six tasks (07 to 12) that a wider integer type cannot
trivialize: in-place `rotate` by any i64 `k` (negative, i64::MIN, empty
array), in-place `dedup` of a sorted array returning the new length, sorted
set `union` of two arrays into a third, stable in-place `partition`,
`windows` (three functions whose contracts must compose: prefix sums, O(1)
range sums, best window of exact width with no window as a sentinel), and a
`vending` state machine over a struct and an enum.

Keel had no `old(...)` at the time, so the in-place tasks pass the Keel function a
read-only copy `orig` of the input for specifications to refer to. Nothing
stops code from reading it too, which makes the in-place part easier in
Keel than in Rust. This describes the binary used for the round 2 run
(hash under "Run notes" below): `old(e)`, `count(&xs, lo, hi, v)` and
`forall v: i64` landed after this run (commit b00de2f), so the next round
can drop `orig` and specify in-place results and permutations directly.
The reference solutions still pass `score.py --ref` on that build.

### Modes

| mode | what the agent gets | what it writes |
|---|---|---|
| `keel` | task.md, PRIMER.md | the whole file, its own contracts (free spec) |
| `keel-given` | task.md, PRIMER.md, `spec.kl` | only function bodies, plus any invariants, helpers, spec fns and lemmas |
| `rust` | task.md | the whole file |

`tasks/*/spec.kl` holds the contract written by us: types, spec fns, and
every function header with `requires`/`ensures` strong enough to pin down
the exact answer (for example, `dedup` must return exactly the set of input
values in strictly increasing order, `partition` must put each element at
its stable position). In `keel-given` mode the scorer compares the types,
spec fns and function headers of the solution with spec.kl, ignoring only
whitespace and comments; any change is outcome `contract_altered`, a
failure whatever the tests say. A `keel-given` pass therefore means the
code is proven to meet a specification the agent did not write.

## Metrics

| metric | meaning |
|---|---|
| pass | hidden tests produce the expected output (and, in `keel-given`, the contract is unchanged) |
| contract altered | `keel-given` only: the solution changed a type, spec fn or function header of spec.kl |
| silent failure | the agent's own toolchain accepted the code, but the hidden tests fail. This is the dangerous case: nothing told the agent it was wrong |
| not done | the agent's own toolchain still rejects the final file (Keel: unproven; Rust: does not compile) |
| proved obligations | facts the Keel verifier machine-checked (overflow, bounds, contracts, termination). Rust's equivalent is 0 beyond type checking |
| spec lines | `requires`/`ensures`/`invariant`/... lines (Keel) or asserts (Rust): how much of the intent is written down where a machine can check it |
| toolchain runs | the agent's self-reported compile/check/test runs per task |

A Keel failure is informative even when it is a failure: "not done" means
the verifier refused to vouch for the code, and that is visible before
anything ships. A Rust silent failure is visible only to the hidden tests.

## Running

```
cargo build --release
python3 evals/score.py --ref                       # validate the harness
python3 evals/score.py evals/results/<run>         # score a run
KEEL_BIN=/path/to/keel python3 evals/score.py ...  # score with a pinned binary
```

A run directory holds `<model>/<mode>/<task>.{kl,rs}` plus each agent's
`report.json`, and optionally `tasks.json` (the task dirs in that run);
scoring writes `scores.md` and `scores.json` next to them.

## Pilot results (2026-10-26)

Full table: `results/pilot-2026-10-26/scores.md`.

| model | lang | hidden-test pass | machine-checked facts | agent tokens | agent seconds |
|---|---|---|---|---|---|
| haiku | keel | 6/6 | 120 | 73k | 91 |
| haiku | rust | 6/6 | 0 | 59k | 42 |
| sonnet | keel | 6/6 | 125 | 56k | 30 |
| sonnet | rust | 6/6 | 0 | 52k | 15 |
| opus | keel | 6/6 | 151 | 58k | 67 |
| opus | rust | 6/6 | 0 | 53k | 38 |

What it shows:

1. **Keel is learnable from one page.** Every model, Haiku included, wrote
   six verifying Keel programs from `PRIMER.md` alone, each passing
   `keel check` on its first run.
2. **The tasks did not discriminate.** All 36 solutions passed the hidden
   tests. Rust has `i128` and `checked_*`, which turn every overflow task
   into a one-liner, and the models know these idioms. Correctness parity
   on easy tasks is expected; the next round needs tasks without escape
   hatches.
3. **The difference is in what is known, not what is correct.** Keel
   solutions carry 120 to 151 machine-checked facts per model; Rust
   solutions carry zero beyond types. Haiku's Rust passing is luck that
   nobody could see beforehand; its Keel passing came with proofs of no
   overflow, no out-of-bounds, termination, and its stated postconditions.
4. **Agents write weak specs when allowed to.** Every model proved only
   `result >= 0` for `gcd` and `max_subarray`, not that the answer is the
   gcd or the maximum. Verification is only as strong as the `ensures`.
   This argues for a "given spec" mode, where the human writes the contract
   and the agent must meet it.
5. **Cost:** Keel took 6 to 39% more tokens and roughly twice the wall
   time (reading the primer, longer files, proof runs).

## Round 2 results (2026-10-26)

Tasks 07 to 12, three modes, one agent per model and mode (prompt:
`AGENT_PROMPT.md`). Full table: `results/round2-2026-10-26/scores.md`.
"Exact contract" counts the tasks whose `ensures` pin down the exact answer
(judged by reading each file against spec.kl; in `keel-given` it holds by
construction once the contract is unchanged and the file verifies).

| model | mode | hidden-test pass | exact contract | machine-checked facts | agent tokens | agent seconds |
|---|---|---|---|---|---|---|
| haiku | keel | 6/6 | 0/6 | 163 | 95k | 211 |
| haiku | keel-given | 6/6 | 6/6 | 339 | 119k | 323 |
| haiku | rust | 6/6 | - | 0 | 68k | 69 |
| sonnet | keel | 6/6 | 3/6 | 294 | 66k | 121 |
| sonnet | keel-given | 6/6 | 6/6 | 332 | 69k | 104 |
| sonnet | rust | 6/6 | - | 0 | 53k | 25 |
| opus | keel | 5/6 | 3/6 | 332 | 65k | 137 |
| opus | keel-given | 6/6 | 6/6 | 342 | 77k | 188 |
| opus | rust | 6/6 | - | 0 | 54k | 28 |

What discriminated:

1. **Contract strength, in free-spec mode.** Left to themselves, Haiku
   wrote no exact contract (no `ensures` at all for `rotate` and
   `vending`, only `0 <= result <= len` for `dedup`, `union` and
   `partition`). Sonnet and Opus each wrote three exact ones (both got
   `rotate` and `dedup`; Sonnet also `union`, Opus also `vending`). No
   model stated stability for `partition` or the meaning of `best_window`.
2. **Given-spec mode closes that gap completely.** With our contracts,
   all three models, Haiku included, proved all six exact specifications,
   mostly on the first `keel check` run, and none altered a contract. They
   found the non-obvious proof techniques themselves: witness arrays
   instead of `exists` invariants, induction lemmas bounding prefix sums
   and counts. Haiku went from 0/6 exact to 6/6 proven exact, for 1.7x the
   tokens and 4.7x the wall time of its Rust run.
3. **Proof stability.** The single failure is not wrong code. Opus's free
   `dedup` verifies on some runs and times out on others (3 of 6 runs of
   `keel check` on the identical file); the agent's own run passed and the
   scorer's run failed. The cause is a quantifier of the form
   `forall t in 0..(n - 1) { xs[t] < xs[t + 1] }`, which gives Z3 a
   matching loop, combined with run-to-run variation in the generated SMT.
   The reference solutions hit the same problem until rewritten with
   pairwise quantifiers (`forall i in 0..n { forall j in i..n { xs[i] <= xs[j] } }`). Keel
   needs deterministic verification and a warning for self-triggering
   quantifiers; until then a verified result can depend on luck.

   **Fixed after this run.** The generated SMT was in fact identical from
   run to run; the variation came from wall-clock timeouts, whose timing
   changed solver state for later checks in the same process. Every check
   now gets a fixed budget of solver work (Z3 `rlimit`), so verdicts are
   deterministic. This file now fails the same way every time, with a hint
   naming the self-triggering quantifier; rewritten pairwise as the hint
   suggests, it proves in 0.77 s, where it previously needed about 110 s of
   solver work.

What did not discriminate:

4. **Hidden tests.** 53 of 54 solutions pass, and all 18 Rust solutions
   pass. Every model avoided every planted trap: `rem_euclid` or a
   non-negative fix-up for negative `k` and i64::MIN, an early return for
   the empty array, headroom comparisons (`v <= 1_000_000 - credit`)
   instead of overflowing additions, i64::MIN rather than 0 as the
   starting best window. Classic edge cases no longer separate these
   models from each other or the two languages from each other.
5. **The in-place part of the array tasks, in Keel.** 16 of the 18 Keel
   solutions to `rotate`, `dedup` and `partition` read from the `orig`
   copy, so in Keel they were copy-out problems rather than in-place ones.
   This is a task-design limit that `old(...)`, added since, removes.

Cost: given-spec Keel used 1.3 to 1.7x the tokens of Rust and 4.2 to 6.6x
the wall time; free-spec Keel 1.2 to 1.4x the tokens.

Run notes: agents and scoring used one pinned keel binary (sha256
`fd28371b...204c1`, built from the tree as of 2026-10-26 09:09) because
the compiler source was being changed at the same time. The scores are a
single sample, and because of point 3 a rescore can flip the Opus `dedup`
cell.

## Next round

- Bugs the models do not already know to avoid: seeded subtle-bug tasks
  (give a plausible but wrong body and ask for a fix or a proof), longer
  multi-function programs where the contracts must compose, and tasks
  whose specs are long enough that reading them is the hard part.
- Rewrite the in-place specs with `old(...)` and `count` (now in Keel) and
  drop `orig`, so in-place tasks cannot copy from it.
- Deterministic verification (fixed SMT emission order and solver seed)
  before trusting single-run results; several samples per cell.
- A Rust-with-specs comparison (for example Kani or Prusti) to separate
  "the language" from "having a verifier".

## Limits

Twelve tasks and one sample per cell is a pilot, not a benchmark: expect
noise. The tasks and the given specs were written by the same author as
the reference solutions, and "exact contract" for free-spec files is a
human judgment, not a mechanical check.
