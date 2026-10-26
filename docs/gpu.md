# `par for` on the GPU

Step 2 of Keel's path to GPUs. Every `par for` whose body the GPU can run
becomes an NVIDIA kernel, one thread per iteration. The program still runs
everywhere: without an NVIDIA driver and device, or with `KEEL_GPU=0`, the
same loop runs on the CPU (OpenMP, see [par-for.md](par-for.md)), with the
same results.

## Safety comes from the same proof

Nothing new is trusted at run time. The verifier already proved, for the
loop as written:

- iterations are independent: no iteration touches a slot another writes
  (`V-RACE`), so they may run in any order, all at once;
- every index is in bounds, no arithmetic overflows i64, no divisor is
  zero, every shift amount is in 0..64, every narrow store fits.

So the kernel, like the C, has no checks. What the GPU path adds is a
second backend for the same proven program, which is why it is tested
differentially: `tests/gpu.sh` runs each program with its kernels on the GPU
and with `KEEL_GPU=0`, and requires identical output.

## What a kernel body may contain

The checker's `par for` rules (`E-PARFOR`) are the GPU rules, and since
step 2 they hold **transitively** over the call graph. A body may not
assign outer variables, do io, allocate, `return` or nest `par`, and
neither may anything it calls, however deep: a callee that allocates,
recurses or runs `par` is rejected at the call in the body, with the chain
(`calling 'step', which calls 'scratch', which allocates an array`).
io needs no transitive check: a non-io fn cannot reach io.

Beyond those rules, one thing keeps a loop on the CPU without being an
error: **struct and enum values** (locals, fields, literals, `match`), which
the PTX backend does not lower yet. `keel build` says so:

```
keel: note: par for at line 9:3 runs on the CPU only: its body uses 's' of type Scale
```

Everything else compiles: i64 and bool locals and outer scalars, `while`
loops, `if`, short-circuit `&&` `||` `==>`, all arithmetic, bitwise and shift
operators, `wrap_<type>`, reads and writes of arrays of every element type
(i8 to i64, u8 to u32), and calls to fns taking scalars, `&`/`&mut` arrays
and slices.

## How it is compiled

**PTX, emitted by Keel itself.** PTX is NVIDIA's virtual instruction set.
The driver compiles it for whatever GPU is present when the program loads
it (and caches the result), so:

- building needs no CUDA toolkit, on any host, macOS included (the tests
  were run on a Linux machine with only the NVIDIA driver installed);
- the binary needs only the driver at run time, loaded with `dlopen`, so
  it has no link-time CUDA dependency and still runs where there is none.

Each kernel is `.entry kl_kN(lo, n, scalars..., (ptr, len) per array)`;
thread `t < n` runs iteration `lo + t`. Callees become `.func`s, arrays are
(pointer, length) pairs and slices are pointer offsets, as in C. Values
live in 64-bit registers, so arithmetic is exactly Keel's i64: `div.s64`
and `rem.s64` truncate toward zero like C, `shr.s64` is arithmetic, and
`+ - *` wrap modulo 2^64, which `wrap_<type>` relies on and the verifier
rules out everywhere else. Narrow elements are sign- or zero-extended on
load and truncated on store. The module targets PTX ISA 7.0 / `sm_70`, so
any Volta-or-newer GPU with a CUDA 11 or newer driver loads it.

**Host side.** For each kernel, a C function copies every array the body
uses to the device, launches `ceil(n / 256)` blocks of 256 threads, waits,
copies the arrays the body writes back, and frees. Arrays the loop only
writes are still copied in, because slots no iteration writes must keep
their values. If anything before the launch completes fails, nothing has
changed and the CPU loop runs instead; a failed launch also turns the GPU
off for the rest of the process (a faulted CUDA context stays faulted).
A failed copy *back* is fatal, since an in-place update cannot be rerun.

Environment:

| variable | effect |
|---|---|
| `KEEL_GPU=0` | never use the GPU |
| `KEEL_GPU=1` | as default, but say why when no GPU is usable |
| `KEEL_GPU_TIMING=1` | per launch: copy-in, kernel and copy-out times |

## Cost model, and what is next

Each launch copies its arrays both ways over PCIe. A kernel that does
little work per byte (the triad benchmark) is dominated by those copies and
is faster on the CPU; a kernel that does real work per element (the LCG
benchmark) is far faster on the GPU. The numbers are in
[par-for.md](par-for.md#measured-gpu). The obvious next steps:

- keep arrays resident on the device across consecutive `par for` loops
  that touch them (the verifier knows exactly which arrays each loop reads
  and writes), and copy back only when the CPU next reads them;
- skip the copy-in of arrays every slot of which the loop provably writes;
- a size threshold below which the CPU is used;
- struct values in kernels;
- reductions (see par-for.md), which on a GPU are a tree, not a loop.

Metal (Apple GPUs) would reuse everything above except the last stage:
the body lowering would target MSL or AIR instead of PTX, and unified
memory removes the copies.
