---
purpose: "fz-ul4.29.5 — spawn-with-captures lift (was forbidden v1)"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 6
budget.codegen.instructions: 53
budget.specs.count: 6
budget.planner.worklist_pops: 12
budget.planner.walk_calls: 12
budget.planner.type_fn_calls: 6
budget.planner.matcher_specs: 0
budget.planner.vars: 17
budget.planner.blocks: 6
budget.planner.stmts: 6
budget.planner.dispatches: 4
---

# spawn_with_captures

fz-ul4.29.5 — spawn-with-captures lift (was forbidden v1)

## Notes

Pre-.29.5, fz_spawn asserted captured.len() == 0. With the stub design,
the closure (including captures) is deep-copied into the new task's
heap, then the closure's code pointer materializes the initial frame.
