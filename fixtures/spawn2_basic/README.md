---
purpose: "fz-siu.12 — spawn/2 with min_heap_size hint behaves identically to spawn/1"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 6
budget.codegen.instructions: 68
budget.specs.count: 4
budget.planner.worklist_pops: 7
budget.planner.walk_calls: 7
budget.planner.type_fn_calls: 4
budget.planner.matcher_specs: 0
budget.planner.vars: 17
budget.planner.blocks: 6
budget.planner.stmts: 10
budget.planner.dispatches: 1
---

# spawn2_basic

fz-siu.12 — spawn/2 accepts a min_heap_size hint alongside the closure. v1:
hint is accepted and ignored. The spawned task runs identically to spawn/1.
