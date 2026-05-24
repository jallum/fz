---
purpose: "inner module addressed both fully-qualified (`Outer.Inner.f`) and via outer-local reference"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 3
budget.codegen.instructions: 18
budget.specs.count: 3
budget.typer.worklist_pops: 6
budget.typer.walk_calls: 6
budget.typer.type_fn_calls: 3
budget.typer.matcher_specs: 0
budget.typer.vars: 26
budget.typer.blocks: 6
budget.typer.stmts: 13
budget.typer.dispatches: 2
---

# nested_modules

inner module addressed both fully-qualified (`Outer.Inner.f`) and via outer-local reference
