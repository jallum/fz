---
purpose: "pipe macro rewrite for call RHS and headless case RHS"
paths: [jit, interp, aot]
budget.codegen.functions: 1
budget.codegen.instructions: 7
budget.specs.count: 1
budget.typer.worklist_pops: 1
budget.typer.walk_calls: 1
budget.typer.type_fn_calls: 1
budget.typer.matcher_specs: 0
budget.typer.vars: 21
budget.typer.blocks: 5
budget.typer.stmts: 11
budget.typer.dispatches: 0
---

# pipe_headless_case

Exercises `lhs |> f(args)` and `lhs |> case do ... end` after pipe handling
moved into macro expansion.
