---
purpose: "TailCallClosure with captured singleton closure-lit preserves narrow arg ABI through recursive HOF"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 5
budget.codegen.instructions: 92
budget.specs.count: 5
budget.typer.worklist_pops: 8
budget.typer.walk_calls: 8
budget.typer.type_fn_calls: 5
budget.typer.matcher_specs: 0
budget.typer.vars: 36
budget.typer.blocks: 12
budget.typer.stmts: 19
budget.typer.dispatches: 4
---

# tailcall_closure_captures

Recursive higher-order call through a captured closure-lit must pass the
list element to the lambda body in the lambda's narrow representation.
