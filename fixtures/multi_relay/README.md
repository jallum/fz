---
purpose: "two workers both block on receive simultaneously; exercises scheduler managing multiple Blocked processes"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 14
budget.codegen.instructions: 178
budget.specs.count: 8
budget.planner.worklist_pops: 16
budget.planner.walk_calls: 16
budget.planner.type_fn_calls: 8
budget.planner.matcher_specs: 0
budget.planner.vars: 36
budget.planner.blocks: 12
budget.planner.stmts: 22
budget.planner.dispatches: 3
---

# multi_relay

two workers both block on receive simultaneously; exercises scheduler managing multiple Blocked processes

## Notes

Both workers call `receive()` before the parent sends to either. Output is deterministic:
pid=2 (first spawn) runs before pid=3 in a FIFO run-queue, so main receives 20 then 22.

This fixture is the acceptance test for the scheduler correctly cycling through
multiple blocked processes across interpreter, JIT, AOT, and REPL script mode.
