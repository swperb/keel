# Bend sources

`bitonic.bend`, `queens.bend`, `histogram.bend` and `matmul.bend` are
copied unchanged from Bend's runtime benchmarks
(`bench/runtime/tree-bitonic`, `bench/runtime/queens`,
`bench/runtime/histogram`, `bench/runtime/tree-matmul`) at
github.com/bendlang/bend commit `e351332b906bb8786cf1d445c3e296804ff43d14`.
`par_sum.bend` is Bend's `demos/pure_par_sum/main.bend` from the same
commit, scaled from d = 16 to d = 30 with a U32 sum (see its header).

Bend is Copyright the Bend authors (HigherOrderCO) and licensed under the
Apache License 2.0: https://github.com/bendlang/bend/blob/main/LICENSE.
These files were checked and built with Bend 2.0.39, the current release.
