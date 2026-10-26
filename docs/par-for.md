# `par for`: data-parallel loops

Step 1 of Keel's path to GPUs: a loop whose iterations run in parallel,
proven race-free like everything else, compiled to OpenMP on the CPU.
The same restrictions are what a GPU kernel body needs (step 2).

## Syntax

```
par for i in lo..hi
  ensures E(i)          // zero or more; what one iteration did
{
  body
}
```

`i` takes every value in `[lo, hi)` (none if `hi <= lo`). `lo` and `hi` are
evaluated once, before any iteration. `i` is an immutable `i64`; like every
Keel name it may not shadow another.

```
fn saxpy(a: i64, xs: &[i64], ys: &mut [i64])
  requires len(ys) == len(xs) && -1000 <= a && a <= 1000
  requires forall k in 0..len(xs) { -1000000 <= xs[k] && xs[k] <= 1000000 }
  requires forall k in 0..len(ys) { -1000000000 <= ys[k] && ys[k] <= 1000000000 }
  ensures forall k in 0..len(ys) { ys[k] == (a * xs[k]) + old(ys[k]) }
{
  par for i in 0..len(ys)
    ensures ys[i] == (a * xs[i]) + old(ys[i])
  {
    ys[i] = (a * xs[i]) + ys[i];
  }
}
```

## What the body may do (checker, `E-PARFOR`)

May:
- declare and assign its own locals (`let`, `var`), branch, `match`, run
  `while` loops (with invariants, as usual), `assert`, invoke lemmas;
- read any array or outer scalar;
- write slots of `&mut` parameters and owned arrays declared outside;
- call `fn`s that are not `io`, not recursive (no `decreases`), and do not
  return an array, passing borrows and slices as usual.

May not:
- assign a variable declared outside the loop: that is loop-carried state,
  and a data race (`E-PARFOR`);
- `print` or call an `io fn` (`E-EFFECT`);
- allocate (`array(..)`, a `let` of an array, a call returning an array);
- `return`; contain `par` or another `par for`.

These are deliberately the restrictions of a GPU kernel. On the CPU,
allocation and recursive callees would be harmless, but keeping one set of
rules means any `par for` that compiles today can become a kernel.
(Callees are checked only directly here; step 2 has to check the call graph
transitively, since a callee may itself allocate or recurse.)

## Proof obligations (verifier)

The body is verified once for an arbitrary iteration `i` with
`lo <= i < hi`, starting from the state before the loop: every usual
obligation (bounds, overflow, division, callee requires, inner-loop
invariants) is proven there, for every `i` at once.

**Race freedom (`V-RACE`).** The verifier symbolically executes a second
copy of the body for another iteration `j`, `lo <= j < hi`, `j != i`, also
from the state before the loop, and records every array access of both
copies: the array, the slot range (one slot `[e, e+1)` for `xs[e]`, the
borrowed range for a call argument `&xs`, `&mut xs[a..b]`), and the path
condition under which it happens. It then proves, for each array:

1. every slot iteration `i` writes is a slot iteration `j` does not write;
2. every slot iteration `i` writes is a slot iteration `j` does not read;
3. every slot the loop's `ensures` reads at `i` is one `j` does not write.

Reads by `j` against writes by `i` cover the converse by symmetry (`i`, `j`
are arbitrary). Path conditions make conditional writes precise:
`if i == 0 { ys[0] = 1; }` is race-free, `if xs[i] > 0 { ys[0] = 1; }` is not.

Index terms may be anything the solver can reason about: `xs[i]`,
`xs[2 * i + 1]`, `out[r * w + c]` inside an inner `while` with invariant
`0 <= c < w` (proven via nonlinear arithmetic), a scatter through a
permutation the precondition describes, or disjoint row slices
`&mut m[r * w..(r + 1) * w]` passed to a callee. This is the injectivity
rule ("`e` is injective in `i` and in range") stated semantically instead of
syntactically, so it admits everything the syntactic rule would and more.
Bounds are separate, ordinary `V-BOUNDS` obligations.

Reads in specifications (asserts, inner-loop invariants, callee contracts)
are ghost: they touch no memory at run time, so they are not accesses.
`old(..)` reads the entry state, which no iteration changes.

**Why that is enough.** Every iteration is verified as if it ran alone from
the pre-loop state. Take any interleaving of real executions. By induction
on the order of memory operations, each read of iteration `j` returns the
pre-loop value, because condition 2 says no other iteration writes that slot
(and the slot index itself was computed from earlier reads, which are
pre-loop values by the induction hypothesis). So every iteration behaves
exactly as verified, writes exactly the slots recorded, and by condition 1
each slot is written by at most one iteration. The final state is the
pre-loop state with each iteration's writes applied, in any order.

## What is known after the loop

No loop invariant is needed, because nothing is carried between iterations.
Instead, each `ensures E(i)` is proven at the end of the body for iteration
`i` (`V-ENSURES`), in the state where only iteration `i` has run. After the
loop the verifier assumes

```
forall i in lo..hi { E(i) }
```

over the final state. That is sound because the final state agrees with
"only `i` ran" on every slot `E(i)` reads: a slot `i` wrote holds `i`'s value
(no one else writes it, condition 1), and any other slot `E(i)` reads is
written by no iteration (condition 3), so it keeps its pre-loop value in both.

Concretely, each array the body may write gets a fresh value after the loop;
lengths, read-only arrays and every scalar are unchanged. Hence:

- Without an `ensures`, nothing is known about a written array's contents
  afterwards (sound, deliberately weak).
- There is no automatic frame: slots of a written array that no iteration
  touches are not known to keep their values. When the caller needs that,
  put the loop in a function taking a `&mut` slice; the call site already
  knows that everything outside the slice is unchanged.
- `old(e)` keeps its meaning (the function's entry state). To relate a slot
  to its value just before the loop, put the loop at the start of a
  function, as in `saxpy` above. Kernels are naturally functions.

The `ensures` reads must stay inside iteration `i`'s own slots of written
arrays (condition 3); `ensures xs[i + 1] == 0` where iteration `i + 1`
writes `xs[i + 1]` is rejected with `V-RACE` even if it happens to be true.

## Reductions: not included

`par for ... reduce s += e` was considered and left out. It is sound only if
the partial sums cannot overflow in any association order the runtime
picks, which is a stronger and less intuitive obligation than the serial
loop's (`+big, -big, +big` fits serially and overflows when regrouped).
A sound version: accumulate in wrapping `uint64_t` (exact modulo 2^64 for
any order), require a proof that the true total fits in `i64`, then the
wrapped result equals it. That is small but deserves its own design pass
together with GPU reductions (step 2). Today, write per-iteration results
to an array and sum serially, or split the range with `par` over slices.

## Compilation

```c
const int64_t lo1 = <lo>, hi1 = <hi>;
#pragma omp parallel for schedule(static)
for (int64_t k_i = lo1; k_i < hi1; k_i++) { <body> }
```

Arithmetic is the same `int64_t` with operand casts as everywhere else, and
no runtime checks are emitted. Every outer variable is shared, which the
proof makes safe; body locals are private by scoping.

When an NVIDIA GPU is present, eligible loops run as GPU kernels instead,
falling back to this CPU loop otherwise ([gpu.md](gpu.md)).

`keel build` adds OpenMP only when the program contains a `par for`. It tries
`-fopenmp` (GCC, LLVM clang), then Apple clang's
`-Xpreprocessor -fopenmp -lomp` against libomp in `$KEEL_LIBOMP`,
`/opt/homebrew/opt/libomp` or `/usr/local/opt/libomp`. If none works it
prints a note and compiles without OpenMP: the pragma is ignored and the
loop runs serially with the same results. `KEEL_NO_OPENMP=1` forces the
serial build, which `tests/run.sh` uses to check that parallel and serial
runs print the same output.

## Measured: Keel `par for` vs Rust rayon

`bench/parfor/run.sh`: the same kernels in Keel (`lcg.kl`, `triad.kl`) and
Rust (`rayon_bench`, `par_iter_mut`), identical `i64` arithmetic and sizes,
outputs asserted equal across all four builds. Wall-clock median of 7 runs
of the whole process (allocation, kernel, serial checksum).

- `lcg`, compute-bound: `out[i]` = 256 LCG steps from `i`, 10M slots.
- `triad`, memory-bound: `zs[i] = 3 * xs[i] + ys[i]`, 50M slots
  (1.2 GB per pass), 21 passes, after a parallel fill of `xs` and `ys`.

| kernel | Keel par for (OpenMP) | Rust rayon | Keel serial | Rust serial | Keel / rayon |
|---|---|---|---|---|---|
| lcg | 0.307 s | 0.307 s | 3.771 s | 3.771 s | 1.00x |
| triad | 0.155 s | 0.204 s | 0.356 s | 0.349 s | 0.76x |

Apple M5 Pro (15 cores: 10 performance, 5 efficiency), macOS, Apple clang
21.0.0 with LLVM libomp 5.0 (OpenMP API), rustc 1.96.0 with rayon 1.12.0,
default thread counts (15 for both). The compute-bound kernel is a tie:
both compile to the same loop and scale 12.3x. On the memory-bound kernel
OpenMP's static schedule beats rayon's recursive splitting; scaling the
pass count (2, 21, 101 passes: 0.059, 0.150, 0.551 s parallel) confirms
about 5 ms per 1.2 GB pass, roughly 240 GB/s, against about 113 GB/s on one
core. "Serial" is Keel built with `KEEL_NO_OPENMP=1` and Rust with plain
iterators. One machine, one session; treat differences under ~10% as noise.

## Measured: GPU

Step 2 ([gpu.md](gpu.md)) runs the same `par for` loops as NVIDIA kernels.
`bench/parfor/gpu.sh` on one Linux machine: AMD Ryzen 5 5600X (6 cores, 12
threads), NVIDIA GeForce RTX 5080 (driver 610.88), Ubuntu 26.04 under WSL2,
gcc 15.2, rustc 1.99.1. Wall-clock medians of 7 whole-process runs; all four
builds print the same checksum. The last column sums `KEEL_GPU_TIMING` over
the run's launches.

| kernel | Keel GPU | Keel CPU (OpenMP) | Keel serial | Rust rayon | GPU: copy in / kernel / copy out |
|---|---|---|---|---|---|
| lcg | 0.339 s | 0.761 s | 4.967 s | 0.574 s | 21.1 / 12.3 / 78.3 ms (1 launch) |
| triad | 4.859 s | 1.226 s | 1.655 s | 1.141 s | 3682 / 32.7 / 2715 ms (23 launches) |

- **lcg** (2.56 billion dependent multiply-and-remainder steps): the kernel
  takes 12.3 ms. Most of the 0.339 s is fixed: starting CUDA and loading the
  kernels costs about 0.28 s per process on this machine (a 1000-element
  program takes 309 ms with the GPU, 33 ms without), and copying the 80 MB
  result back takes 78 ms.
- **triad** (one multiply-add per 24 bytes): the GPU loses by 4x. The
  kernels total 33 ms, roughly 850 GB/s, but every launch copies its three
  400 MB arrays in and the written one out over PCIe: 6.4 s of copies for
  23 launches over the same, unchanged inputs. Keeping arrays on the device
  between loops is the fix (gpu.md, "what is next").
- On this CPU rayon beats Keel's OpenMP build on lcg (0.574 s vs 0.761 s)
  and the two tie on triad; on the M5 Pro above they tied on lcg. The
  difference is the C compiler and OpenMP runtime (gcc/libgomp here, clang
  and LLVM's libomp there), not the generated loop.

## Measured: f32

`bench/parfor/logistic.kl` ([f32.md](f32.md)): 256 steps of
`x = (3.9 * x) * (1.0 - x)` in f32 for each of 10M slots, then a serial
checksum of the bits. Every build on both machines, Keel on the CPU, Keel
on the GPU and Rust, prints the same checksum (3047852245): the results
are bit-identical. Same method as above (medians of 7 whole-process runs).

| machine | Keel GPU | Keel CPU (OpenMP) | Keel serial | Rust rayon | Rust serial |
|---|---|---|---|---|---|
| M5 Pro, 15 cores | n/a | 0.216 s | 2.461 s | 0.210 s | 2.457 s |
| Ryzen 5 5600X + RTX 5080 | 0.272 s | 0.447 s | 0.813 s | 0.322 s | n/a |

On the RTX 5080 the kernel itself takes 0.8 ms (copy in 11.2 ms, copy out
51.7 ms); the rest of the 0.272 s is the fixed cost of starting CUDA
(about 0.28 s per process on that machine, see above), so for this size
the GPU wins only once that cost is shared by more work in one process.
The other kernels, measured in the same run on the Ryzen machine: lcg GPU
0.323 s, OpenMP 0.741 s, rayon 0.576 s; triad GPU 4.766 s, OpenMP 1.205 s,
rayon 1.127 s (consistent with the step-2 table).
