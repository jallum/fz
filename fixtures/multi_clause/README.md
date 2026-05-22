---
purpose: "multi-clause dispatch with a guard clause (`when n > 0`), plus recursive `fact`"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 7
budget.codegen.instructions: 20
budget.specs.count: 13
budget.typer.worklist_pops: 34
budget.typer.walk_calls: 34
budget.typer.type_fn_calls: 13
budget.typer.matcher_specs: 0
budget.typer.vars: 83
budget.typer.blocks: 28
budget.typer.stmts: 39
budget.typer.dispatches: 27
---

# multi_clause

multi-clause dispatch with a guard clause (`when n > 0`), plus recursive `fact`
