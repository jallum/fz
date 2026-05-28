---
purpose: "irrefutable tuple destructure in a let-style bind — first fixture to exercise `{a, b} = expr` across all four legs"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 21
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 16
budget.planner.blocks: 2
budget.planner.stmts: 10
budget.planner.dispatches: 0
---

# destructure_tuple

`{a, b} = pair()` — the simplest non-trivial destructure: irrefutable
tuple bind in expression position, on a value the planner can statically
prove is a 2-tuple. Pre-fz-fyq this either failed to compile under
warnings-as-errors (unreachable-arm noise on the synthesized fail
funnel) or compiled with a dead Halt(:match_error) block; this fixture
locks parity and silence across all four legs.
