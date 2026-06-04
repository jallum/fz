# Fixtures

A fixture is a small `.fz` program under `fixtures/<name>/` that proves one
thing about the language and proves it on every execution path that applies.
`tests/fixture_matrix.rs` is the harness: it discovers every fixture directory,
reads each `README.md` frontmatter, and runs `input.fz` through the paths the
fixture declares, scoring each run against goldens. The same file also holds a
set of static trials (the Elixir oracle, the index check, dump budgets, outcome
goldens, CLIF-shape proofs) that don't fit the per-path mould.

## Anatomy

```text
fixtures/<name>/
  input.fz                     the program
  README.md                    frontmatter + optional prose
  expected.txt                 stdout golden (optional)
  expected.<path>.txt          per-path stdout golden (optional, overrides expected.txt)
  expected.diagnostics         stderr/diagnostic golden (optional)
  expected.<path>.diagnostics  per-path diagnostic golden (optional)
  expected.stderr              stderr substring golden for `expect: abort`
  expected.<path>.stderr       per-path stderr substring golden (optional)
  expected.outcomes            per-callsite planner-verdict golden (optional)
  oracle.exs                   Elixir twin whose stdout owns expected.txt (optional)
```

`discover()` returns every directory under `fixtures/` that contains an
`input.fz`. The matrix derives every other sidecar path from the directory.

### Frontmatter

The README opens with a `---`-delimited block parsed by `parse_header_from_dir`.
It is a tiny YAML subset, only the keys below:

- `purpose:` — the one-line description (required). Single source of truth for
  the fixture's headline; `fixtures/index.md` is regenerated from it.
- `paths:` — flow sequence of the paths to run, e.g. `[jit, interp, aot, repl]`
  (required). Empty `[]` is allowed only with a `defer:` rationale.
- `kind:` — `run` or `test`. Defaults to `run` when `input.fz` defines a `main`,
  otherwise `test`. Decides which jit subcommand runs (see the matrix).
- `expect:` — `success` (default), `abort`, or `diagnostic` (the pass/fail
  contract; see below).
- `diagnostic.code:` — for `expect: diagnostic` fixtures, the telemetry code to
  assert (e.g. `spec/violation`).
- `defer:` — a rationale, required when `paths:` is empty. The fixture then runs
  nowhere and surfaces as an ignored trial carrying the rationale.
- `oracle:` — relative path to an Elixir twin whose stdout owns `expected.txt`.
- `timeout.<path>_secs:` — per-path wall-clock timeout override.
- `budget.<namespace>.<metric>:` — a compiler-shape target counter (see Dump
  budgets).

The prose body after the frontmatter is a plain statement of present-tense facts
about what the fixture proves. It is optional and carries no code: the code is
`input.fz`. Most fixtures are frontmatter-only.

## The four-path matrix

Each declared path becomes its own `cargo test` trial named
`matrix::<fixture>::<path>`. `cargo test add1` filters to one fixture;
`cargo test ::repl` filters to one leg across all fixtures. `run_path` drives
each path:

| path     | driver                                                            |
|----------|-------------------------------------------------------------------|
| `jit`    | `fz run <input.fz>` (or `fz test` when `kind: test`)              |
| `interp` | `fz interp <input.fz>`                                            |
| `aot`    | `fz build <input.fz> -o <tmp>` then run the binary                |
| `repl`   | `fz repl --script <input.fz>`                                     |

The `aot` and `repl` legs only run `kind: run` fixtures; a `kind: test` fixture
is surfaced as `Deferred` on those legs because `fz test` is jit-only.

Each runner captures a `Ran { success, stdout, diagnostics }` with *no* verdict
applied. `check()` then applies the fixture's `expect:` policy in one place, so
the pass/fail rule is not re-derived per path.

### Pass/fail rules

`expect: success` (the default): the path passes when the process exits 0 **and**
stdout matches its golden **and** diagnostics match their golden. Goldens resolve
per-path-first: `expected.<path>.txt` if present else `expected.txt`, likewise
for `.diagnostics`. An absent golden means "expect empty" — the path must produce
no stdout (or no diagnostics). Any nonzero exit fails before output is compared.

A fixture flips that contract to pin a *negative* claim:

- `expect: abort` — a run-time abort. The path passes when the process exits
  *nonzero* and its stderr **contains** the `expected.stderr` golden as a
  substring. A substring (not exact match) keeps per-path prefixes
  (`fz interp:`, `repl:`) and absolute source paths out of the pin.
- `expect: diagnostic` — a compile-time rejection. Same nonzero-exit
  requirement, but when the fixture declares `diagnostic.code`, the matrix
  reruns the path with telemetry and asserts a `["fz","diag","error"]` event
  carrying that code; rendered stderr is free to change. Without
  `diagnostic.code` it falls back to the `expected.stderr` substring check.

For `aot`, build and run are distinct steps. `expect: success`/`abort` require
the build to succeed first, then judge the binary's exit. `expect: diagnostic`
expects the *build itself* to fail, so the build outcome is what `check()` judges
— there is no binary to run.

Exit code 75 (EX_TEMPFAIL) from a declared path marks it not-yet-wired
(`RunOutcome::Deferred`): the trial reports the reason on stderr and passes. The
default per-fixture execution timeout is `FIXTURE_COMMAND_TIMEOUT` = 3s and
covers execution only: jit/interp/repl start the clock when the program signals
it is ready to run, and the `aot` build is an untimed step before the binary's
run is timed. A `timeout.<path>_secs` override raises that wall-clock limit for
one path while keeping it in correctness coverage.

### BLESS

`BLESS=1 cargo test fixture_matrix` rewrites `expected.txt` /
`expected.<path>.txt` and `.diagnostics` from current output, and seeds a missing
`expected.stderr` with full captured stderr (the author then trims it to the
stable line). On a non-bless failure the actual output is dropped at
`<dir>/actual.txt`, `actual.diagnostics`, or `actual.stderr` for diffing. These
`actual.*` files are gitignored.

### The Elixir oracle

A fixture that declares `oracle: oracle.exs` makes "matches Elixir" a mechanical
diff. The single static trial `oracle_goldens_match_elixir` runs every oracle
script under the real `elixir` binary and asserts its stdout equals
`expected.txt`. The per-path matrix trials independently assert each fz path
reproduces that same `expected.txt`, so `fz == Elixir` holds transitively.
Elixir owns the golden: under `BLESS=1` the oracle trial regenerates
`expected.txt`, and per-path bless never rewrites it for an oracle fixture. The
oracle is a hard prerequisite, not an optional skip — a missing or failing
`elixir` is a loud failure. CI installs Elixir (1.19) through `erlef/setup-beam`.

## The media

A fixture pins its claim in the most direct medium for what it tests.
`fixtures/GOLDEN.md` holds the choosing rule and the per-fixture map.

1. **In-language assertion** — `assert(expr == expected, "why")` / `refute`.
   The program checks itself and aborts on failure, so the claim is verified on
   every path with no golden file. The default for behavioural claims.
2. **Rendering golden** — `dbg(x)` + `expected.txt`, when the rendered string
   itself is the artifact (how a value prints).
3. **Memory-floor stats** — `Process.heap_alloc_stats()` + a per-path golden.
   Allocation counts are cross-run and path-variant: native reuses cons cells,
   interp/repl are direct-IR baselines, and jit equals aot. No single in-program
   assertion expresses a cross-run relationship, so these stay golden. The
   matrix has no cross-leg check — each leg resolves its own golden per-path-first
   (`expected.<path>.txt` else `expected.txt`) and matches that. So where native
   parity is expected (`enum_sort`, `process_heap_stats`, `quicksort`) jit and aot
   each ship their own `expected.jit.txt` / `expected.aot.txt`; the two are kept
   byte-identical so jit == aot, but that equality is a property of the maintained
   files, not something the harness enforces.
4. **Compiler-shape budget** — `budget.*` frontmatter (see Dump budgets).
5. **Expect-failure** — `expect: abort` / `expect: diagnostic`. The only medium
   that pins what the language must *refuse*: the program must abort (run-time)
   or be rejected (compile-time). Positive media (assertions, goldens) can only
   say what it must accept.

## Dump budgets

`budget.*` frontmatter pins compiler shape across three namespaces:
`budget.codegen.*` (lowered function and instruction counts), `budget.specs.count`,
and `budget.planner.*` (planner work counters — worklist pops, walk/type-fn
calls, matcher specs, spec var/block/stmt counts, dispatches). The static
`dump_budgets` trial runs `fz dump --emit stats <input.fz>` with telemetry on,
reads the counters from the `fz.codegen.function_lowered` and authoritative
`fz.planner.planned` events, and checks each declared target.

`check_budget_metric` allows a symmetric band of ±`DUMP_BUDGET_TOLERANCE_PERCENT`
(20%) around each target. A budget measures a runnable program, so it lives on a
fixture with a `main`; a `main`-less runtime-library module is budgeted through a
fixture that exercises it. A failing budget writes `fixtures/<name>/actual.clif`
and `actual.specs` as local debugging artifacts (gitignored). Budgets have no
BLESS step — the frontmatter target is hand-updated in the same commit as the
change that moves it.

## Outcome goldens

A fixture that ships `expected.outcomes` opts into the static `golden_outcomes`
trial, which runs `fz dump --emit outcomes` (a per-callsite planner-verdict
diary) and asserts an exact match against the sidecar. This is independent of the
per-path matrix and skips `kind: test` and deferred fixtures.

## Relationship to the runtime library

Behavioural fixtures call the same runtime library that user programs do
(`Kernel.assert`/`refute`/`panic`, `Enum`, `Enumerable`, `Process`), so the
assertion machinery a fixture uses is itself fz source under
`src/modules/runtime_library/`. `assert`/`refute` route a failure through
`Kernel.panic`, which calls the `fz_panic` extern; that is why a failed assertion
is a nonzero exit on every path. A fixture that exercises a runtime-library
function both proves the function and (via budgets and allocation goldens) pins
its compiled shape and allocation floor.
