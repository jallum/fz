---
purpose: "VR.5a — int-int / atom-atom equality lowers to a single icmp, no fz_value_eq dispatch"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 3
budget.codegen.instructions: 30
budget.specs.count: 3
budget.planner.worklist_pops: 6
budget.planner.walk_calls: 6
budget.planner.type_fn_calls: 3
budget.planner.matcher_specs: 0
budget.planner.vars: 38
budget.planner.blocks: 7
budget.planner.stmts: 20
budget.planner.dispatches: 2
---

# vr5a_typed_eq

VR.5a — int-int / atom-atom equality lowers to a single icmp, no fz_value_eq dispatch

## Notes

`1 == 2` and `:ok == :err`: ir_planner narrows both operands to int / atom
monomorphic Descrs. VR.5a's lower_eq fires the same-kind scalar arm:
tagged AnyValues for a given scalar kind compare by bit equality, so the
emit is a single icmp eq + bool_to_fz. No both_ptr tag dispatch, no
fz_value_eq call site.
