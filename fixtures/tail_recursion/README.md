---
purpose: "100k-deep self-recursion must TCO — exits cleanly with the accumulated count"
paths: [jit, interp, aot]
budget.codegen.functions: 4
budget.codegen.instructions: 58
budget.specs.count: 4
budget.typer.worklist_pops: 10
budget.typer.walk_calls: 10
budget.typer.type_fn_calls: 5
budget.typer.matcher_specs: 0
budget.typer.vars: 26
budget.typer.blocks: 8
budget.typer.stmts: 16
budget.typer.dispatches: 4
repl-skip: "eval::Interp lacks TCO; 100k self-recursion overflows the host stack"
---

# tail_recursion

100k-deep self-recursion must TCO — exits cleanly with the accumulated count
