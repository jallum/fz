---
purpose: "irrefutable tuple destructure in a let-style bind — first fixture to exercise `{a, b} = expr` across all four legs"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 2
budget.codegen.instructions: 22
budget.specs.count: 3
budget.typer.worklist_pops: 4
budget.typer.walk_calls: 4
budget.typer.type_fn_calls: 3
budget.typer.matcher_specs: 0
budget.typer.vars: 47
budget.typer.blocks: 10
budget.typer.stmts: 19
budget.typer.dispatches: 2
---

# destructure_tuple

`{a, b} = pair()` — the simplest non-trivial destructure: irrefutable
tuple bind in expression position, on a value the typer can statically
prove is a 2-tuple. Pre-fz-fyq this either failed to compile under
warnings-as-errors (unreachable-arm noise on the synthesized fail
funnel) or compiled with a dead Halt(:match_error) block; this fixture
locks parity and silence across all four legs.
