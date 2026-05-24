---
purpose: "two workers both block on receive simultaneously; exercises scheduler managing multiple Blocked processes"
paths: [jit, interp, aot]
budget.codegen.functions: 14
budget.codegen.instructions: 532
budget.specs.count: 8
budget.typer.worklist_pops: 16
budget.typer.walk_calls: 16
budget.typer.type_fn_calls: 8
budget.typer.matcher_specs: 0
budget.typer.vars: 36
budget.typer.blocks: 12
budget.typer.stmts: 22
budget.typer.dispatches: 3
---

# multi_relay

two workers both block on receive simultaneously; exercises scheduler managing multiple Blocked processes

## Notes

Both workers call `receive()` before the parent sends to either. Output is deterministic:
pid=2 (first spawn) runs before pid=3 in a FIFO run-queue, so main receives 20 then 22.

This fixture is the acceptance test for the scheduler correctly cycling through multiple
blocked processes. Promote to paths: [jit, interp, aot] once fz-sched.1+fz-sched.3 land.
