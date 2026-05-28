---
purpose: "receive matcher supports heap map keys without allocating inside matcher probes"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 18
budget.codegen.instructions: 439
budget.specs.count: 15
budget.planner.worklist_pops: 38
budget.planner.walk_calls: 38
budget.planner.type_fn_calls: 15
budget.planner.matcher_specs: 0
budget.planner.vars: 75
budget.planner.blocks: 15
budget.planner.stmts: 31
budget.planner.dispatches: 8
---

# receive_map_heap_keys

fz-puj.51 — float and UTF-8 binary map-pattern keys are prepared before
the selective receive matcher runs. The matcher receives stable key
values through synthetic key slots and only performs probes, tests, and
branches while scanning the mailbox.
