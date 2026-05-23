---
purpose: "receive matcher supports heap map keys without allocating inside matcher probes"
paths: [jit, interp, aot]
budget.codegen.functions: 29
budget.codegen.instructions: 550
budget.specs.count: 19
budget.typer.worklist_pops: 32
budget.typer.walk_calls: 32
budget.typer.type_fn_calls: 19
budget.typer.matcher_specs: 0
budget.typer.vars: 135
budget.typer.blocks: 43
budget.typer.stmts: 63
budget.typer.dispatches: 12
---

# receive_map_heap_keys

fz-puj.51 — float and UTF-8 binary map-pattern keys are prepared before
the selective receive matcher runs. The matcher receives stable key
values through synthetic key slots and only performs probes, tests, and
branches while scanning the mailbox.
