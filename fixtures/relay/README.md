---
purpose: "one-hop relay — spawned child blocks on receive before parent sends; exercises non-blocking spawn + receive-parks semantics"
paths: [jit, interp, aot]
budget.codegen.functions: 10
budget.codegen.instructions: 219
budget.specs.count: 6
budget.typer.worklist_pops: 10
budget.typer.walk_calls: 10
budget.typer.type_fn_calls: 6
budget.typer.matcher_specs: 0
budget.typer.vars: 23
budget.typer.blocks: 8
budget.typer.stmts: 13
budget.typer.dispatches: 1
---

# relay

one-hop relay — spawned child blocks on receive before parent sends; exercises non-blocking spawn + receive-parks semantics

## Notes

The child calls `receive()` before the parent has had a chance to call `send(2, 41)`.
Under correct BEAM semantics: child parks, parent continues, parent sends, child wakes,
child sends result back to parent.

Currently only [jit] because the JIT cooperative scheduler runs the parent first (main
is already executing when spawn returns; child is merely enqueued). Interp and AOT run
the child eagerly at spawn time, hitting receive on an empty mailbox.

This fixture is the acceptance test for fz-sched.1 (AOT) and fz-sched.3 (interp):
once those land, promote to paths: [jit, interp, aot].
