---
purpose: "fibonacci via two-accumulator tail recursion — three-clause dispatch + tail-call forwarding under load"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 4
budget.codegen.instructions: 17
budget.specs.count: 4
budget.typer.worklist_pops: 9
budget.typer.walk_calls: 9
budget.typer.type_fn_calls: 4
budget.typer.matcher_specs: 0
budget.typer.vars: 36
budget.typer.blocks: 8
budget.typer.stmts: 24
budget.typer.dispatches: 6
---

# fib_tailrec

fibonacci via two-accumulator tail recursion — three-clause dispatch + tail-call forwarding under load
