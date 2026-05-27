---
purpose: "one-hop relay — spawned child blocks on receive before parent sends; exercises non-blocking spawn + receive-parks semantics"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 7
budget.codegen.instructions: 94
budget.specs.count: 5
budget.planner.worklist_pops: 9
budget.planner.walk_calls: 9
budget.planner.type_fn_calls: 5
budget.planner.matcher_specs: 0
budget.planner.vars: 20
budget.planner.blocks: 5
budget.planner.stmts: 10
budget.planner.dispatches: 1
---

# relay

one-hop relay — spawned child blocks on receive before parent sends; exercises non-blocking spawn + receive-parks semantics

## Notes

The child calls `receive()` before the parent has had a chance to call `send(2, 41)`.
Under correct BEAM semantics: child parks, parent continues, parent sends, child wakes,
child sends result back to parent.

The scheduler must run the parent first: `spawn` enqueues the child and returns,
the child may park on `receive`, and the later parent send must wake it.
