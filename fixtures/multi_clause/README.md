---
purpose: "multi-clause dispatch with a guard clause (`when n > 0`), plus recursive `fact`"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 7
budget.codegen.instructions: 32
budget.specs.count: 7
budget.typer.worklist_pops: 18
budget.typer.walk_calls: 18
budget.typer.type_fn_calls: 7
budget.typer.matcher_specs: 0
budget.typer.vars: 53
budget.typer.blocks: 16
budget.typer.stmts: 27
budget.typer.dispatches: 6
---

# multi_clause

multi-clause dispatch with a guard clause (`when n > 0`), plus recursive `fact`
