---
purpose: "two-hop process relay — main → first_relay → second_relay → main; exercises multi-process message chaining"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 14
budget.codegen.instructions: 185
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

The interpreter, JIT, AOT, and REPL script paths all use the cooperative
scheduler semantics needed for the relays to park and resume in order.
