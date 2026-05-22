---
purpose: "defmacro + quote/unquote round-trip — two macros, one nested in the other"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 3
budget.codegen.instructions: 13
budget.specs.count: 3
budget.typer.worklist_pops: 6
budget.typer.walk_calls: 6
budget.typer.type_fn_calls: 3
budget.typer.matcher_specs: 0
budget.typer.vars: 26
budget.typer.blocks: 6
budget.typer.stmts: 17
budget.typer.dispatches: 2
---

# macro_inc

defmacro + quote/unquote round-trip — two macros, one nested in the other
