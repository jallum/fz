---
purpose: "receive matcher supports heap map keys without allocating inside matcher probes"
paths: [jit, interp, aot]
budget.codegen.min_functions: 27
budget.codegen.max_functions: 27
budget.codegen.min_instructions: 523
budget.codegen.max_instructions: 785
budget.specs.min_count: 26
budget.specs.max_count: 40
---

# receive_map_heap_keys

fz-puj.51 — float and UTF-8 binary map-pattern keys are prepared before
the selective receive matcher runs. The matcher receives stable key
values through synthetic key slots and only performs probes, tests, and
branches while scanning the mailbox.
