---
purpose: "VR.2 — float-literal arithmetic + comparisons emit native fadd/fcmp, no dispatch"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 3
budget.codegen.instructions: 27
budget.specs.count: 3
budget.typer.worklist_pops: 6
budget.typer.walk_calls: 6
budget.typer.type_fn_calls: 3
budget.typer.matcher_specs: 0
budget.typer.vars: 38
budget.typer.blocks: 7
budget.typer.stmts: 20
budget.typer.dispatches: 2
---

# vr2_float_arith

VR.2 — float-literal arithmetic + comparisons emit native fadd/fcmp, no dispatch

## Notes

fz-ul4.27.15.2: float literals consumed by float-monomorphic vars lower
straight to `f64const` without a heap allocation round-trip.

Both operands of each op are Float literals → ir_typer narrows to float
→ lower_prim's descr_is_float branch fires → native fadd/fsub/fmul +
fcmp. Post-.27.15.2, Const::Float emits raw f64 directly when the
consumer is float-monomorphic; the previous heap allocation path is gone.
