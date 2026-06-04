---
purpose: "VR.5a — int-int / atom-atom equality lowers to a single icmp, no fz_value_eq dispatch"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 26
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 17
budget.planner.blocks: 1
budget.planner.stmts: 16
budget.planner.dispatches: 0
---

# vr5a_typed_eq

VR.5a — int-int / atom-atom equality lowers to a single icmp, no fz_value_eq dispatch

## Notes

`1 == 2` and `:ok == :err`: ir_planner narrows both operands to int / atom
monomorphic Descrs. VR.5a's lower_eq fires the same-kind scalar arm:
tagged AnyValues for a given scalar kind compare by bit equality, so the
emit is a single icmp eq + bool_to_fz. No both_ptr tag dispatch, no
fz_value_eq call site.
