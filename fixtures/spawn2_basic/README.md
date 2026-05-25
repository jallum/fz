---
purpose: "fz-siu.12 — spawn/2 with min_heap_size hint behaves identically to spawn/1"
paths: [jit, interp, aot]
budget.codegen.functions: 6
budget.codegen.instructions: 68
budget.specs.count: 4
budget.typer.worklist_pops: 5
budget.typer.walk_calls: 5
budget.typer.type_fn_calls: 4
budget.typer.matcher_specs: 0
budget.typer.vars: 17
budget.typer.blocks: 6
budget.typer.stmts: 10
budget.typer.dispatches: 0
---

# spawn2_basic

fz-siu.12 — spawn/2 accepts a min_heap_size hint alongside the closure. v1:
hint is accepted and ignored. The spawned task runs identically to spawn/1.
