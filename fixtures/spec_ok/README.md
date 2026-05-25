---
purpose: "fz-ul4.31.6 — declared @spec matches inferred behavior;"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 3
budget.codegen.instructions: 21
budget.specs.count: 3
budget.typer.worklist_pops: 5
budget.typer.walk_calls: 5
budget.typer.type_fn_calls: 3
budget.typer.matcher_specs: 0
budget.typer.vars: 11
budget.typer.blocks: 4
budget.typer.stmts: 5
budget.typer.dispatches: 2
---

# spec_ok

fz-ul4.31.6 — declared @spec matches inferred behavior;

## Notes

         runs identically on interp, jit, aot
