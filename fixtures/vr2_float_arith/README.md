---
purpose: "VR.2 — float-literal arithmetic + comparisons emit native fadd/fcmp, no dispatch"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 3
budget.codegen.instructions: 28
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

# vr2_float_arith

VR.2 — float-literal arithmetic + comparisons emit native fadd/fcmp, no dispatch

## Notes

fz-ul4.27.15.2: float literals consumed by float-monomorphic vars lower
straight to `f64const` without a heap allocation round-trip.

Both operands of each op are Float literals → ir_planner narrows to float
→ lower_prim's descr_is_float branch fires → native fadd/fsub/fmul +
fcmp. Post-.27.15.2, Const::Float emits raw f64 directly when the
consumer is float-monomorphic; the previous heap allocation path is gone.
