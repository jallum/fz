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
  expected.stderr          stderr substring golden for `expect: abort|diagnostic`
  expected.outcomes        planner-dispatch golden (optional)
```

README frontmatter carries `purpose`, `paths`, an optional `expect:`, optional
path-specific `timeout.<path>_secs` overrides, and any `budget.*` targets.
`fixtures/index.md` is generated from the frontmatter; regenerate it with
`BLESS=1 cargo test fixture_index_up_to_date` after editing a fixture.

The README prose is a plain statement of facts about the current state — what
the fixture proves, in present tense, no adornment and no chronology. It carries
no code: the code is `input.fz`, and a code block in a README is duplication.
The `purpose:` line is the single source of the one-line description; the prose
body below the frontmatter is optional and present only when it adds something
`purpose:` does not. Most fixtures are frontmatter-only.

## The four-path matrix

`tests/fixture_matrix.rs` runs each fixture on the paths its `paths:` lists:

| path     | driver                       |
|----------|------------------------------|
| `jit`    | `fz run <input.fz>`          |
| `interp` | `fz interp <input.fz>`       |
| `aot`    | `fz build` then run the binary |
| `repl`   | `fz repl --script <input.fz>`|

By default (`expect: success`) a path passes when the process exits successfully
**and** stdout matches the golden **and** diagnostics match the golden. An absent
golden means "expect empty": a fixture with no `expected.txt` must produce no
stdout. A nonzero exit is then a failure. A fixture can flip that contract with
`expect: abort` (run-time panic) or `expect: diagnostic` (compile-time
rejection): the path passes only when the process exits *nonzero* and its stderr
contains the `expected.stderr` golden as a substring — this is how a fixture
pins a negative claim (see medium 5 below). Exit code 75 marks a path as
not-yet-wired (`Deferred`), which is reported but does not fail. The default
per-fixture execution timeout is 3s. A `timeout.<path>_secs` override keeps a
path in correctness coverage while temporarily relaxing that performance gate;
the fixture README must name the ticket that restores the default.

Fixtures whose README frontmatter declares `oracle: oracle.exs` add one static
fixture-matrix trial: `oracle_goldens_match_elixir` runs the oracle script with
the real `elixir` binary and asserts its stdout equals `expected.txt`. This is a
hard prerequisite, not an optional skip. Local oracle verification and CI both
require Elixir 1.19+ on PATH; CI installs Elixir through `erlef/setup-beam`.

## The media

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
5. **Expect-failure** — `expect: abort` / `expect: diagnostic` + `expected.stderr`.
   Pins a *negative* claim: the program must abort (run-time) or be rejected
   (compile-time). The path passes when the process exits nonzero and its stderr
   contains the golden as a substring. This is the only medium that lets a
   fixture assert what the language must *refuse*; positive media (assertions,
   goldens) can only say what it must accept.

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
