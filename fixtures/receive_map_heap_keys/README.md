---
purpose: "receive matcher supports heap map keys without allocating inside matcher probes"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 26
budget.codegen.instructions: 574
budget.specs.count: 23
budget.planner.worklist_pops: 23
budget.planner.walk_calls: 23
budget.planner.type_fn_calls: 23
budget.planner.matcher_specs: 0
budget.planner.vars: 72
budget.planner.blocks: 23
budget.planner.stmts: 28
budget.planner.dispatches: 31
---

# receive_map_heap_keys

fz-puj.51 — float and UTF-8 binary map-pattern keys are prepared before
the selective receive matcher runs. The matcher receives stable key
values through synthetic key slots and only performs probes, tests, and
branches while scanning the mailbox.
