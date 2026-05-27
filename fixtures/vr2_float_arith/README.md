---
purpose: "VR.2 — float-literal arithmetic + comparisons emit native fadd/fcmp, no dispatch"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 18
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 21
budget.planner.blocks: 1
budget.planner.stmts: 16
budget.planner.dispatches: 0
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
