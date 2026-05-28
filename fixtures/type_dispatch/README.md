---
purpose: multi-clause fn dispatches on parameter type at runtime (fz-ty1.8/1.9)
paths: [interp, jit, aot, repl]
budget.codegen.functions: 2
budget.codegen.instructions: 10
budget.specs.count: 2
budget.planner.worklist_pops: 3
budget.planner.walk_calls: 3
budget.planner.type_fn_calls: 2
budget.planner.matcher_specs: 0
budget.planner.vars: 18
budget.planner.blocks: 4
budget.planner.stmts: 8
budget.planner.dispatches: 1
---

`fn check(x :: integer)` emits a `TypeTest` guard that dispatches to the
integer clause for integer arguments and to the fallback clause for atoms.
Proves fz-ty1.8 (parser), fz-ty1.9 (lowering), and fz-ty1.6 (TypeTest codegen).
