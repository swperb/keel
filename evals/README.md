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

## Metrics

| metric | meaning |
|---|---|
| pass | hidden tests produce the expected output |
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
```

A run directory holds `<model>/<lang>/<task>.{kl,rs}` plus each agent's
`report.json`; scoring writes `scores.md` and `scores.json` next to them.

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

## Next round

- Tasks without library escape hatches: in-place array algorithms
  (partition, dedup, merge, rotate), multi-function programs, struct state
  machines.
- **Given-spec mode**: the task ships the Keel `requires`/`ensures`; the
  agent writes only the body. Correct-by-proof becomes measurable.
- Several samples per cell, and seeded subtle-bug tasks to measure how
  often each toolchain catches a planted logic error.

## Limits

Six tasks and one sample per cell is a pilot, not a benchmark: expect noise.
The next steps are more tasks (array mutation, structs, multi-function
programs), several samples per cell, token and wall-clock accounting, and
a Keel-without-specs ablation to separate "the language" from "writing the
spec down".
