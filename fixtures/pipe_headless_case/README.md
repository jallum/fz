---
purpose: "pipe macro rewrite for call RHS and headless case RHS"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 3
budget.codegen.instructions: 8
budget.specs.count: 7
budget.planner.worklist_pops: 7
budget.planner.walk_calls: 7
budget.planner.type_fn_calls: 7
budget.planner.matcher_specs: 0
budget.planner.vars: 17
budget.planner.blocks: 10
budget.planner.stmts: 9
budget.planner.dispatches: 6
---

# pipe_headless_case

Exercises `lhs |> f(args)` and `lhs |> case do ... end` after pipe handling
moved into macro expansion.
