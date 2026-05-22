---
purpose: multi-clause fn dispatches on parameter type at runtime (fz-ty1.8/1.9)
paths: [interp, jit, aot]
budget.codegen.functions: 3
budget.codegen.instructions: 10
budget.specs.count: 4
budget.typer.worklist_pops: 8
budget.typer.walk_calls: 8
budget.typer.type_fn_calls: 4
budget.typer.matcher_specs: 0
budget.typer.vars: 30
budget.typer.blocks: 9
budget.typer.stmts: 12
budget.typer.dispatches: 6
---

`fn check(x :: integer)` emits a `TypeTest` guard that dispatches to the
integer clause for integer arguments and to the fallback clause for atoms.
Proves fz-ty1.8 (parser), fz-ty1.9 (lowering), and fz-ty1.6 (TypeTest codegen).
