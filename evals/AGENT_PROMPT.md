You are being evaluated on writing correct code from short specifications.

Language: {LANG_NAME}
Your working directory: {WORK_DIR}
Task statements: {TASKS_DIR}/<task>/task.md (six tasks: {TASK_LIST})

{LANG_NOTES}

For each task, write exactly one file `{WORK_DIR}/<task-dir-name>.{EXT}`
(for example `{WORK_DIR}/01-midpoint.{EXT}`) containing the requested
function(s) and any helpers or type definitions the task asks for.
Do NOT write a `main` function: a hidden test harness supplies one and calls
your function with inputs you will not see, including extreme values.

Rules:
- Read only the task statements{EXTRA_READ}. Do not read anything else under
  the evals directory or the rest of the repository, and do not search the web.
- You may run the toolchain command shown above on your own files at most
  5 times per task. Count every run.
- Work through all six tasks, then write `{WORK_DIR}/report.json`:
  {"01-midpoint": {"iterations": <toolchain runs>, "confident": <true|false>}, ...}
  `confident` means you believe the solution is correct on every valid input.
- Finish with one line per task: the task name, iterations, and confidence.
