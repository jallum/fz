---
purpose: "receive matcher supports heap map keys without allocating inside matcher probes"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 22
budget.codegen.instructions: 556
budget.specs.count: 19
budget.planner.worklist_pops: 47
budget.planner.walk_calls: 47
budget.planner.type_fn_calls: 19
budget.planner.matcher_specs: 0
budget.planner.vars: 101
budget.planner.blocks: 31
budget.planner.stmts: 47
budget.planner.dispatches: 12
---

# receive_map_heap_keys

fz-puj.51 — float and UTF-8 binary map-pattern keys are prepared before
the selective receive matcher runs. The matcher receives stable key
values through synthetic key slots and only performs probes, tests, and
branches while scanning the mailbox.
