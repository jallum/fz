---
purpose: "minimal call site — one fn definition, one call, no scaffolding"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 5
budget.specs.count: 1
budget.typer.worklist_pops: 1
budget.typer.walk_calls: 1
budget.typer.type_fn_calls: 1
budget.typer.matcher_specs: 0
budget.typer.vars: 9
budget.typer.blocks: 2
budget.typer.stmts: 5
budget.typer.dispatches: 0
---

# cold_fn

minimal call site — one fn definition, one call, no scaffolding
