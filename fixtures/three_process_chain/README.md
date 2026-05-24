---
purpose: "two-hop process relay — main → first_relay → second_relay → main; exercises multi-process message chaining"
paths: [jit, interp, aot]
budget.codegen.functions: 14
budget.codegen.instructions: 505
budget.specs.count: 8
budget.typer.worklist_pops: 13
budget.typer.walk_calls: 13
budget.typer.type_fn_calls: 8
budget.typer.matcher_specs: 0
budget.typer.vars: 34
budget.typer.blocks: 10
budget.typer.stmts: 20
budget.typer.dispatches: 1
---

# three_process_chain

two-hop process relay — main → first_relay → second_relay → main; exercises multi-process message chaining

## Notes

PIDs are deterministic: main=1, first_relay=2, second_relay=3 (spawn order).
main sends 40 to pid=2; each relay increments by 1; main receives 42.

JIT-only: interp and AOT use eager-sync (spawn runs child to completion immediately),
so a child that calls receive() before its sender runs deadlocks. The JIT cooperative
scheduler runs main first, letting it pre-load first_relay's mailbox before yielding.

Promote to paths: [jit, interp, aot] once fz-sched.1+fz-sched.3 land.
