You are being evaluated on writing correct code from short specifications.

Language: {LANG_NAME}
Your working directory: {WORK_DIR}
Task statements: {TASKS_DIR}/<task>/task.md ({N} tasks: {TASK_LIST})

{LANG_NOTES}

For each task, write exactly one file `{WORK_DIR}/<task-dir-name>.{EXT}`
(for example `{WORK_DIR}/{FIRST_TASK}.{EXT}`) containing the requested
function(s) and any helpers or type definitions the task asks for.
Do NOT write a `main` function: a hidden test harness supplies one and calls
your function with inputs you will not see, including extreme values.

Rules:
- Read only the task statements{EXTRA_READ}. Do not read anything else under
  the evals directory or the rest of the repository, and do not search the web.
- You may run the toolchain command shown above on your own files at most
  5 times per task. Count every run. Put any scratch files (ad hoc tests)
  in {SCRATCH}, not in your working directory.
- Work through all {N} tasks, then write `{WORK_DIR}/report.json`:
  {"{FIRST_TASK}": {"iterations": <toolchain runs>, "confident": <true|false>}, ...}
  `confident` means you believe the solution is correct on every valid input.
- Finish with one line per task: the task name, iterations, and confidence.

Language notes used in round 2 (filled in for {LANG_NOTES}):

- Keel, free spec: "Keel is described in {PRIMER} (read it first). Check a
  file with `{KEEL} check <file.kl>`; a file that does not pass `keel check`
  counts as not done. Write whatever requires/ensures you consider right."
- Keel, given spec: the free-spec note, plus: "Each task directory also has
  `spec.kl`, the contract written by the task author: types, spec fns, and
  every function's signature with its requires/ensures. Start your file from
  a copy of spec.kl, keep all of that text exactly as given (whitespace and
  comments aside), and write only the function bodies. You may add loop
  invariants, asserts, helper functions, spec fns and lemmas. A file whose
  contract differs from spec.kl scores as a failure even if it works."
- Rust: "Check a file with `rustc --edition 2021 --crate-type lib <file.rs>`.
  You may write ad hoc tests in scratch files."
