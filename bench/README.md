# Keel vs Rust vs Bend, on Bend's programs

Issue #4 suggests earning the claim "as fast as Bend on CPU, with proofs
Bend doesn't give", measured on Bend's own programs. This directory holds
those programs in three languages, a runner, and the measured results in
[RESULTS.md](RESULTS.md).

| program | from Bend | what it does |
|---|---|---|
| `par_sum` | `demos/pure_par_sum` | fork/join sum of 0 .. 2^30, recursing to single numbers |
| `bitonic` | `bench/runtime/tree-bitonic` | bitonic sorting network over 2^23 hashed u32 keys, then a tree scan that checks sortedness and folds a checksum |
| `msort` | (same task as `bitonic`) | the same keys, scan and checksum, sorted by Keel's verified mergesort |
| `queens` | `bench/runtime/queens` | 17-queens by bitmask backtracking under a 2^17-leaf fork tree |
| `histogram` | `bench/runtime/histogram` | 128 rounds of a 256-bucket histogram of 2^24 keys, in 2^11 blocks |
| `matmul` | `bench/runtime/tree-matmul` | 384 rounds of 128 x 128 quad-tree matrix multiply in wrapping u32, with a Freivalds check |

Every program prints the checksum Bend's program prints, and the runner
rejects any run whose output differs. Bend's sources are in `bend/`
(unchanged, except `par_sum`, see below; license in `bend/NOTICE.md`),
Keel's in `keel/`, Rust's in `rust/`.

## Running

```
python3 bench/run.py              # everything, 5 timed runs per cell
python3 bench/run.py --runs 3 --only queens,histogram
```

Needs cargo, z3 and cc (as Keel does) and Bend 2 (`bend` on PATH, or
`BEND=/path/to/bend`). Install Bend with `curl -fsSL
https://bend-lang.com/install.sh | sh` (set `BEND_HOME` to install
elsewhere). Without Bend, its columns read "not measured".

For each program the runner:

1. runs `keel check` (timed) and `keel build --emit-c`. It also compiles
   a 1-core variant of the same C with the `par` spawner capped at one
   live thread, so every `par` runs inline. Keel has no thread-count
   option, so this is how the 1-core column is made.
2. builds the Rust twin, which takes `seq` (one thread) or `par`
   (`rayon::join` at the same fork points and cutoffs as the Keel `par`).
3. compiles Bend's program the way Bend's own benchmark gate does
   (`bend f.bend -o f.c`, then `cc -std=c11 -O3`, plus the Metal build on
   macOS or CUDA on Linux) and runs it with the gate's flags:
   `+RTS --threads 1 --gpu off`, `+RTS --threads N --gpu off` (N = the
   smallest power of two at or above the core count), and `+RTS --gpu
   <mem>` for the GPU.
4. runs each configuration once to warm up, then `--runs` times, and
   reports the median run's wall time and CPU time (user + system, from
   `wait4`).

It writes `RESULTS.md` and `results/results.json` (every sample).

## Porting notes

- Bend's trees become arrays whose halves (or quarters) are the subtrees,
  and every fork in Bend becomes a `par` over disjoint slices. In
  `bitonic`, Bend builds its leaves in a different order. Any correct sort
  of the same keys gives the same array, so the checksum still matches.
  In `matmul` the matrices are in Z-order, so each quadrant is a
  contiguous slice; the product accumulates into its output (C += A B),
  which in wrapping u32 equals Bend's P + Q at every node.
- `par_sum`: Bend's demo sums 2^16 numbers as a `Nat`, and Bend's `Nat`
  stops at 2^48, so past d = 24 the demo cannot run. The Bend version here
  sums 2^30 numbers as a U32 (the sum mod 2^32). Keel and Rust compute the
  exact sum in i64 and also print it mod 2^32. All three recurse down to
  single numbers. A serial loop at the leaves would be turned into a
  closed form by LLVM, and then nothing would be timed.
- `queens`: Keel's verifier reasons about `& | ^ ~` through 64-bit
  vectors, which is slow for masks that are not constants. So the u32
  bit operations are reduced with `wrap_u32` (exactly C's and Bend's U32
  semantics), the board size is fixed at 17 as in Bend's C twin, and the
  candidate loop terminates by a 32-step fuel bound. Bend's own port uses
  a fuel argument for termination too.
- `histogram`: Bend's program has a two-step column pass for tables of
  2^12 rows or more. At this size (2^11 rows) it takes the one-step path,
  which is the one ported.
- Cutoffs: Keel and Rust fork above the same sizes (2^16 numbers or
  elements for sums, fills and scans, 2^12 for sort steps, 2^6 leaves for
  queens, every level for histogram and matmul). Keel's runtime forks only
  while a core is free (an OS thread per fork); rayon uses work stealing.

## Caveats

- Bend's runtime picks its own task granularity; Keel and Rust use the
  explicit cutoffs above. Each language is run as its authors' benchmark
  harness runs it, not with matched thread counts.
- The machine is shared. `RESULTS.md` records the load average before
  the run.
