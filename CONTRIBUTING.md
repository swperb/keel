# Contributing to Keel

Thanks for helping. Keel is small on purpose; the bar for new features is
"does this remove ambiguity or prevent a class of bugs?", not "is this
convenient?".

## Ground rules

1. **One way to do it.** Proposals that add a second syntax or a second way
   to express an existing idea will be declined. Open an issue to discuss
   language changes before writing code.
2. **Soundness first.** A verifier change must never make an unprovable
   program pass. Every soundness fix ships with a test in `tests/reject/`
   that failed before the fix.
3. **No new dependencies.** The compiler builds with `cargo` and nothing
   else from crates.io. External tools are limited to `z3` and a C compiler.
4. **Errors are an API.** Error codes (`E-*`, `V-*`) are stable. A new
   diagnostic gets a new code, an entry in `keel explain`, and a hint an
   agent can act on.
5. **Plain prose.** Docs, comments and commit messages are direct and
   specific. No marketing language.

## Development

```
cargo build --release
./tests/run.sh
```

`tests/run.sh` runs every example (they must prove and print the expected
output) and every file in `tests/reject/` (each must fail with the error
code named on its first line, `// expect: CODE`).

Requirements: Rust (stable), `z3` 4.8 or newer on PATH (or `KEEL_Z3`), and
a C11 compiler (`CC`, default `cc`).

## Pull requests

- `main` is protected: changes land through pull requests that pass CI.
- Keep PRs focused; one feature or fix per PR.
- Run `cargo fmt` and `./tests/run.sh` before pushing.
- Describe what the change proves or rejects that it did not before.

## Contributor License Agreement

By submitting a contribution (code, documentation, tests or other material)
to this repository, you agree to the following:

1. You wrote the contribution, or otherwise have the right to submit it
   under these terms.
2. You license your contribution to the project owner (swperb) under the
   AGPL-3.0 **and** grant the project owner a perpetual, worldwide,
   non-exclusive, royalty-free, irrevocable license to use, modify,
   sublicense and relicense it under any terms, including proprietary and
   commercial licenses.
3. You grant everyone who receives the software a patent license for any
   patent claims you can license that are necessarily infringed by your
   contribution, on the terms of section 11 of the AGPL-3.0.
4. You keep the copyright to your contribution.

This lets the project offer commercial licenses (see `LICENSING.md`) while
the code stays open source. Pull requests state agreement by including this
line in the PR description:

```
I agree to the Keel Contributor License Agreement in CONTRIBUTING.md.
```
