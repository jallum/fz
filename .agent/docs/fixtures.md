# Fixtures

A fixture is a small `.fz` program under `fixtures/<name>/` that proves one
thing about the language and proves it on every execution path that applies.

## Anatomy

```text
fixtures/<name>/
  input.fz                 the program
  README.md                frontmatter + prose
  expected.txt             stdout golden (optional)
  expected.<path>.txt      per-path stdout golden (optional, overrides expected.txt)
  expected.diagnostics     stderr/diagnostic golden (optional)
  expected.<path>.diagnostics  per-path diagnostic golden (optional)
  expected.outcomes        planner-dispatch golden (optional)
```

README frontmatter carries `purpose`, `paths`, and any `budget.*` targets.
`fixtures/index.md` is generated from the frontmatter; regenerate it with
`BLESS=1 cargo test fixture_index_up_to_date` after editing a fixture.

## The four-path matrix

`tests/fixture_matrix.rs` runs each fixture on the paths its `paths:` lists:

| path     | driver                       |
|----------|------------------------------|
| `jit`    | `fz run <input.fz>`          |
| `interp` | `fz interp <input.fz>`       |
| `aot`    | `fz build` then run the binary |
| `repl`   | `fz repl --script <input.fz>`|

A path passes when the process exits successfully **and** stdout matches the
golden **and** diagnostics match the golden. An absent golden means "expect
empty": a fixture with no `expected.txt` must produce no stdout. A nonzero exit
(including a `Kernel.panic` abort) is a failure, scored before any output
comparison — so a fixture cannot both abort and pass. Exit code 75 marks a path
as not-yet-wired (`Deferred`), which is reported but does not fail. The
per-fixture execution timeout is 3s.

## The four media

A fixture pins its claim in the most direct medium for what it tests:

1. **In-language assertion** — `assert(expr == expected, "why")` / `refute`.
   The program checks itself and aborts on failure, so the claim is verified on
   every path with no golden file. The default for behavioural claims.
2. **Rendering golden** — `dbg(x)` + `expected.txt`, when the rendered string
   itself is the artifact (how a value prints).
3. **Memory-floor stats** — `Process.heap_alloc_stats()` + a per-path golden.
   Allocation counts are cross-run and path-variant: native reuses cons cells,
   interp/repl are direct-IR baselines, and JIT equals AOT. No single in-program
   assertion expresses a cross-run relationship, so these stay golden.
4. **Compiler-shape budget** — `budget.*` frontmatter.

`fixtures/GOLDEN.md` holds the choosing rule and the per-fixture map.

## Dump budgets

`budget.*` frontmatter pins compiler shape: codegen function and instruction
counts, spec counts, and planner work counters. `cargo test --test
fixture_matrix dump_budgets` runs `fz dump --emit stats <input.fz>`, which
compiles the program with telemetry on and compares the emitted counters against
the targets within the band set by `DUMP_BUDGET_TOLERANCE_PERCENT`. A budget
measures a runnable program, so it lives on a fixture with a `main`; a
`main`-less runtime-library module is budgeted through a fixture that exercises
it. A failing budget writes `fixtures/<name>/actual.clif` and `actual.specs` as
local debugging artifacts; these are not checked in. Budgets have no BLESS step —
update the frontmatter by hand in the same commit as the change that moves it.

## Relationship to the runtime library

Behavioural fixtures call the same runtime library that user programs do
(`Kernel.assert`/`refute`/`panic`, `Enum`, `Enumerable`, `Process`), so the
assertion machinery a fixture uses is itself fz source under
`src/modules/runtime_library/`. A fixture that exercises a runtime-library
function both proves the function and pins its compiled shape and allocation
floor.
