---
purpose: "irrefutable tuple destructure in a let-style bind — first fixture to exercise `{a, b} = expr` across all four legs"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 2
budget.codegen.instructions: 30
budget.specs.count: 2
budget.typer.worklist_pops: 3
budget.typer.walk_calls: 3
budget.typer.type_fn_calls: 2
budget.typer.matcher_specs: 0
budget.typer.vars: 30
budget.typer.blocks: 6
budget.typer.stmts: 13
budget.typer.dispatches: 1
---

# destructure_tuple

`{a, b} = pair()` — the simplest non-trivial destructure: irrefutable
tuple bind in expression position, on a value the typer can statically
prove is a 2-tuple. Pre-fz-fyq this either failed to compile under
warnings-as-errors (unreachable-arm noise on the synthesized fail
funnel) or compiled with a dead Halt(:match_error) block; this fixture
locks parity and silence across all four legs.
