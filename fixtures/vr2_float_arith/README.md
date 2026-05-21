---
purpose: "VR.2 — float-literal arithmetic + comparisons emit native fadd/fcmp, no dispatch"
paths: [jit, interp, aot, repl]
---

# vr2_float_arith

VR.2 — float-literal arithmetic + comparisons emit native fadd/fcmp, no dispatch

## Notes

fz-ul4.27.15.2: float literals consumed by float-monomorphic vars lower
straight to `f64const` — no `fz_alloc_float` heap round-trip.

Both operands of each op are Float literals → ir_typer narrows to float
→ lower_prim's descr_is_float branch fires → native fadd/fsub/fmul +
fcmp. Post-.27.15.2, Const::Float emits raw f64 directly when the
consumer is float-monomorphic; the previous heap round-trip through
fz_alloc_float is gone.
