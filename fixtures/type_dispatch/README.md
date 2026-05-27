---
purpose: multi-clause fn dispatches on parameter type at runtime (fz-ty1.8/1.9)
paths: [interp, jit, aot, repl]
budget.codegen.functions: 3
budget.codegen.instructions: 17
budget.specs.count: 3
budget.planner.worklist_pops: 6
budget.planner.walk_calls: 6
budget.planner.type_fn_calls: 3
budget.planner.matcher_specs: 0
budget.planner.vars: 25
budget.planner.blocks: 7
budget.planner.stmts: 10
budget.planner.dispatches: 2
---

`fn check(x :: integer)` emits a `TypeTest` guard that dispatches to the
integer clause for integer arguments and to the fallback clause for atoms.
Proves fz-ty1.8 (parser), fz-ty1.9 (lowering), and fz-ty1.6 (TypeTest codegen).
