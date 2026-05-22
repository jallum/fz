---
purpose: "fz-ht5 — make_ref() returns a distinct opaque ref on every call"
paths: [jit, interp, aot]
budget.codegen.functions: 1
budget.codegen.instructions: 6
budget.specs.count: 1
budget.typer.worklist_pops: 1
budget.typer.walk_calls: 1
budget.typer.type_fn_calls: 1
budget.typer.matcher_specs: 0
budget.typer.vars: 9
budget.typer.blocks: 1
budget.typer.stmts: 3
budget.typer.dispatches: 0
---

# make_ref_distinct

fz-ht5 — Two successive calls to `make_ref()` must return distinct values. The
value's type is the opaque `ref`; arithmetic on it is rejected by the typer
(separate fixture / negative test).
