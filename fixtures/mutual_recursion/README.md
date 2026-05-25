---
purpose: "mutual recursion — is_even/is_odd call each other; exercises cross-function recursive dispatch"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 4
budget.codegen.instructions: 31
budget.specs.count: 4
budget.typer.worklist_pops: 9
budget.typer.walk_calls: 9
budget.typer.type_fn_calls: 4
budget.typer.matcher_specs: 0
budget.typer.vars: 28
budget.typer.blocks: 8
budget.typer.stmts: 16
budget.typer.dispatches: 3
---

# mutual_recursion

mutual recursion — is_even/is_odd call each other; exercises cross-function recursive dispatch
