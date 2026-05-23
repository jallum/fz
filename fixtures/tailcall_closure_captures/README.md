---
purpose: "TailCallClosure with captured singleton closure-lit preserves narrow arg ABI through recursive HOF"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 6
budget.codegen.instructions: 479
budget.specs.count: 6
budget.typer.worklist_pops: 13
budget.typer.walk_calls: 13
budget.typer.type_fn_calls: 6
budget.typer.matcher_specs: 0
budget.typer.vars: 44
budget.typer.blocks: 14
budget.typer.stmts: 22
budget.typer.dispatches: 6
---

# tailcall_closure_captures

Recursive higher-order call through a captured closure-lit must pass the
list element to the lambda body in the lambda's narrow representation.
