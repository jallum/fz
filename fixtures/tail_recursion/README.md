---
purpose: "100k-deep self-recursion must TCO — exits cleanly with the accumulated count"
paths: [jit, interp, aot]
budget.codegen.functions: 3
budget.codegen.instructions: 39
budget.specs.count: 3
budget.typer.worklist_pops: 6
budget.typer.walk_calls: 6
budget.typer.type_fn_calls: 3
budget.typer.matcher_specs: 0
budget.typer.vars: 17
budget.typer.blocks: 6
budget.typer.stmts: 10
budget.typer.dispatches: 3
repl-skip: "eval::Interp lacks TCO; 100k self-recursion overflows the host stack"
---

# tail_recursion

100k-deep self-recursion must TCO — exits cleanly with the accumulated count
