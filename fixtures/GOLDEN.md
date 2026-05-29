# Fixture Conventions

A fixture is a tiny `.fz` program under `fixtures/<name>/` that proves something
about the language. Each fixture pins its claim in the **most direct medium** for
what it is actually testing. This file defines those media, the rule for choosing
between them, and the realignment map for the current suite.

See `.agent/docs/fixtures.md` for the holistic orientation (anatomy, the
four-path matrix, pass/fail mechanics, the BLESS workflow).

## The four media

A fixture proves its claim through one (occasionally two) of these:

1. **In-language assertion** — `assert(expr == expected, "why")` / `refute(...)`.
   The claim is a value equality or boolean invariant. The program checks itself
   and aborts (`Kernel.panic`) on failure, which the matrix scores as a failure
   on *every* path. No golden file. This is the default for behavioural claims.

2. **Rendering golden** — `dbg(x)` + `expected.txt`. Use only when the *rendered
   string itself* is the artifact under test (how a value prints), not merely a
   proxy for a value equality.

3. **Memory-floor stats** — `Process.heap_alloc_stats()` + (per-path) golden.
   Pins allocation counts/bytes. These are intrinsically cross-run and
   path-variant (native reuses cons cells; interp/repl are direct-IR baselines;
   JIT must equal AOT), so they stay harness-level — no single in-program
   assertion can express "JIT equals AOT".

4. **Compiler-shape budget** — `budget.*` frontmatter, checked by
   `fz dump --emit stats` against a ±20% band. Pins codegen/planner shape
   (instruction counts, spec counts, planner work). Use when the *shape* is the
   point. (Detail below.)

A fixture may also carry an `expected.outcomes` planner-dispatch golden — a
structural pin on how calls lower to specs/continuations.

## Choosing rule

> Pin in the medium your *purpose* requires. One fixture, one job.

- Purpose is "this feature computes / dispatches / matches correctly" →
  **assertion**, no golden.
- Purpose is "this value renders as exactly this string" → **rendering golden**.
- Purpose is "this allocates exactly this much" → **memory-floor stats**.
- Purpose is "this lowers to this shape" → **budget** (and/or `expected.outcomes`).

Behavioural correctness is path-invariant, so an assertion runs all four paths
for free. Compiler-shape and memory facts are not the program's behaviour, so
they do not belong in the program; they stay as frontmatter budgets and stats
goldens respectively. Do **not** add an assertion to a shape-primary fixture: the
`assert` adds IR (an `==`, an `if`, a panic branch) and pollutes the very shape
it pins.

## Realignment map

Decision for the current suite (the executable subset of this is the `fz-6df`
conversion arc):

**Assertion (behavioural-primary; convert `dbg`→`assert`, drop golden + budget):**
`classify_two_clause`, `wildcard_then_specific`, `type_dispatch`,
`multi_clause_body_with_call`, `destructure_tuple`, `destructure_cons`,
`destructure_mixed`, `case_tuple_pattern_sequential`, `mutual_recursion`,
`tail_recursion`, `list_primitives`, `higher_order`, `apply2`, `polymorphic`,
`utf8_equality`, `utf8_pattern_match`, `utf8_smart_constructor`, `keyword_lists`,
`guard_calls_pure_user_fn`, `map_three_path_parity`, `nested_tuple_producer`,
`relay`, `multi_relay`, `three_process_chain`, `concurrency_ping_pong`,
`actor_ring`, `spawn2_basic`, `spawn_with_captures`. Template:
`make_ref_distinct`, `assert_message`.

**Assertion via `__info__` (module-structure; gated on the `__info__` feature):**
`attributes`, `import`, `alias`, `modules`, `nested_modules`, `fn_ref_ampersand`,
`macro_inc`, `cross_module_macro`.

**Keep rendering golden (the string is the artifact):** `hello`,
`utf8_literal_print`, `empty_list_distinct_from_nil`.

**Keep budget — shape-primary (assert would pollute the pin):** the `vr*` group
(`vr1_int_arith`, `vr2_float_arith`, `vr3_int_args`, `vr3_float_args`,
`vr3_4_typed_capture`, `vr4_2_native_call`, `vr5a_typed_eq`, `vr5a_cross_kind_eq`,
`vr5b_typed_print`), `add1`, `cold_fn`, `hot_fn`, `if_constant_cond_with_call`,
`if_tail_call_in_arm_narrowed`, `if_tail_call_in_arm_unnarrowed`,
`tailcall_closure_captures`, `multi_caller_spec_divergent`, `interp_only_main`,
`spec_ok`, `spec_boundary`, `shared_heap_send_large_bitstring`, and the
`receive_*` family (their `matcher_specs` budget pins `SwitchKind` parity).

**Keep `expected.outcomes` / dispatch pins (converting would shift the graph):**
`multi_clause`, `fib_tailrec`, `curried_add`, `ast_eval`, `closure_typed_captures`.

**Keep memory-floor stats (harness-level):** `append`, `reverse`, `filter`,
`tree`, `quicksort`, `enum_sort`, `enum_list_allocations`, `enum_reduce_suspend`,
`process_heap_stats`, `opaque_fn_value_join`. Budgets realigned case by case
(`quicksort` keeps its budget).

**Keep golden — observed side-effect ordering:** `resource_lifecycle`,
`file_resource_lifecycle`, `file_handle`, `resource_aot_dtor` (the dtor firing is
observed through printed output order).


---

# Fixture Dump Budgets

Fixture dump shape is checked with telemetry-backed budgets in each fixture's
`README.md` frontmatter. The fixture harness runs
`fz dump --emit stats <fixture>/input.fz` with JSON telemetry enabled and
compares compiler-emitted counters against those targets.

This keeps the review signal without committing generated CLIF/spec dumps. The
compiler reports the facts we care about directly:

- `budget.codegen.functions`
- `budget.codegen.instructions`
- `budget.specs.count`
- `budget.planner.worklist_pops`
- `budget.planner.walk_calls`
- `budget.planner.type_fn_calls`
- `budget.planner.matcher_specs`
- `budget.planner.vars`
- `budget.planner.blocks`
- `budget.planner.stmts`
- `budget.planner.dispatches`

Budget values are targets. The fixture harness derives the acceptance band from
`DUMP_BUDGET_TOLERANCE_PERCENT` in `tests/fixture_matrix.rs`, so the policy stays
in one place.

A budget can only be measured against a runnable program: `fz dump --emit stats`
compiles a fixture with a `main`. There is no per-module budget for a `main`-less
runtime-library module (e.g. `enum.fz`); its shape is pinned through a fixture
that exercises it.

## Workflow

Run the budget trial:

```sh
cargo test --test fixture_matrix dump_budgets
```

When a budget passes, no CLIF or specs artifact is produced. When a budget
fails, the harness writes:

- `fixtures/<name>/actual.clif`
- `fixtures/<name>/actual.specs`

Those files are local debugging artifacts. They explain the failed budget, but
they are not checked in and there is no bless step for them.

## Updating Budgets

If an intentional compiler change shifts a fixture's shape, update the target
values in that fixture's README frontmatter in the same commit as the code
change. Review the metrics first. If the failure wrote `actual.clif` or
`actual.specs`, use them to understand the structural change, then remove the
local artifacts before committing.

Runtime stdout/diagnostic fixtures still use their existing `BLESS=1` workflow.
Dump budgets do not.

## Why Budgets

Full dump files made every codegen or planner change legible, but they also kept
thousands of generated lines in the repo and forced every test run to
pretty-print CLIF/specs just to prove nothing surprising happened.

Telemetry budgets ask the compiler for the underlying facts instead: function
bodies lowered, instruction counts, spec counts, matcher specs, and planner work
counters. That is cheaper to run, easier to review, and still catches broad shape
regressions. When a number moves outside the accepted band, the harness produces
the full CLIF/specs on demand.
