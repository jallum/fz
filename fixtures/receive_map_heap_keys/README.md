---
purpose: "receive matcher supports heap map keys without allocating inside matcher probes"
paths: [jit, interp, aot]
budget.codegen.functions: 27
budget.codegen.instructions: 654
budget.specs.count: 15
budget.typer.worklist_pops: 24
budget.typer.walk_calls: 24
budget.typer.type_fn_calls: 15
budget.typer.matcher_specs: 0
budget.typer.vars: 129
budget.typer.blocks: 39
budget.typer.stmts: 63
budget.typer.dispatches: 8
---

# receive_map_heap_keys

fz-puj.51 — float and UTF-8 binary map-pattern keys are prepared before
the selective receive matcher runs. The matcher receives stable key
values through synthetic key slots and only performs probes, tests, and
branches while scanning the mailbox.
