---
purpose: VR.5b — dbg boxes across the any extern ABI and narrows by spec on return
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 12
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 11
budget.planner.blocks: 1
budget.planner.stmts: 6
budget.planner.dispatches: 0
---

# vr5b_typed_print

VR.5b — dbg boxes across the any extern ABI and narrows by spec on return

## Notes

`dbg(x)` crosses the extern boundary as `fz_dbg_value(any) :: any`:
typed scalar args are boxed before the call. The public `dbg(t) :: t`
spec then drives return ABI selection, so typed callers unbox the
boxed `any` result naturally at the wrapper return boundary. Float
debug rendering is shared by the boxed path so `4.0` remains `4.0`.
