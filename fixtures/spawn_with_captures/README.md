---
purpose: "fz-ul4.29.5 — spawn-with-captures lift (was forbidden v1)"
paths: [jit, interp, aot]
budget.codegen.functions: 6
budget.codegen.instructions: 146
budget.specs.count: 6
budget.typer.worklist_pops: 10
budget.typer.walk_calls: 10
budget.typer.type_fn_calls: 6
budget.typer.matcher_specs: 0
budget.typer.vars: 20
budget.typer.blocks: 8
budget.typer.stmts: 9
budget.typer.dispatches: 3
---

# spawn_with_captures

fz-ul4.29.5 — spawn-with-captures lift (was forbidden v1)

## Notes

Pre-.29.5, fz_spawn asserted captured.len() == 0. With the stub design,
the closure (including captures) is deep-copied into the new task's
heap, then the closure's stub_fp materializes the initial frame.
