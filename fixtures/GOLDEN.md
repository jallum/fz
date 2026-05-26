# Fixture Dump Budgets

Fixture dump shape is checked with telemetry-backed budgets in each
fixture's `README.md` frontmatter. The fixture harness runs
`fz dump --emit stats <fixture>/input.fz` with JSON telemetry enabled and
compares compiler-emitted counters against those targets.

This keeps the review signal without committing generated CLIF/spec dumps.
The compiler reports the facts we care about directly:

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

Budget values are targets. The fixture harness derives the acceptance band
from `DUMP_BUDGET_TOLERANCE_PERCENT` in `tests/fixture_matrix.rs`, so the
policy stays in one place.

## Workflow

Run the budget trial:

```sh
cargo test --test fixture_matrix dump_budgets
```

When a budget passes, no CLIF or specs artifact is produced. When a budget
fails, the harness writes:

- `fixtures/<name>/actual.clif`
- `fixtures/<name>/actual.specs`

Those files are local debugging artifacts. They explain the failed budget,
but they are not checked in and there is no bless step for them.

## Updating Budgets

If an intentional compiler change shifts a fixture's shape, update the
target values in that fixture's README frontmatter in the same commit as
the code change. Review the metrics first. If the failure wrote
`actual.clif` or `actual.specs`, use them to understand the structural
change, then remove the local artifacts before committing.

Runtime stdout/diagnostic fixtures still use their existing `BLESS=1`
workflow. Dump budgets do not.

## Why Budgets

Full dump files made every codegen or planner change legible, but they also
kept thousands of generated lines in the repo and forced every test run to
pretty-print CLIF/specs just to prove nothing surprising happened.

Telemetry budgets ask the compiler for the underlying facts instead:
function bodies lowered, instruction counts, spec counts, matcher specs,
and planner work counters. That is cheaper to run, easier to review, and
still catches broad shape regressions. When a number moves outside the
accepted band, the harness produces the full CLIF/specs on demand.
