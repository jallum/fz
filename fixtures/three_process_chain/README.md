---
purpose: "two-hop process relay — main → first_relay → second_relay → main; exercises multi-process message chaining"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 10
budget.codegen.instructions: 185
budget.specs.count: 8
budget.planner.worklist_pops: 13
budget.planner.walk_calls: 13
budget.planner.type_fn_calls: 8
budget.planner.matcher_specs: 0
budget.planner.vars: 34
budget.planner.blocks: 10
budget.planner.stmts: 20
budget.planner.dispatches: 1
---

# three_process_chain

two-hop process relay — main → first_relay → second_relay → main; exercises multi-process message chaining

## Notes

PIDs are deterministic: main=1, first_relay=2, second_relay=3 (spawn order).
main sends 40 to pid=2; each relay increments by 1; main receives 42.

The interpreter, JIT, AOT, and REPL script paths all use the cooperative
scheduler semantics needed for the relays to park and resume in order.
