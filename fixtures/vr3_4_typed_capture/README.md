---
purpose: VR.3.4 / VR.4.3 — typed captures survive cont handoffs via native chain
paths: [jit, interp, aot, repl]
budget.codegen.functions: 4
budget.codegen.instructions: 26
budget.specs.count: 4
budget.planner.worklist_pops: 4
budget.planner.walk_calls: 4
budget.planner.type_fn_calls: 4
budget.planner.matcher_specs: 0
budget.planner.vars: 12
budget.planner.blocks: 4
budget.planner.stmts: 5
budget.planner.dispatches: 3
---

# vr3_4_typed_capture

VR.3.4 / VR.4.3 — typed captures survive cont handoffs via native chain

## Notes

`use_x(x)` takes a typed-int param x (narrowed from main's int-lit
call site). Inside use_x, `double(x) + x` requires x to live across
the call to double — x is captured into the continuation k_3.

Under VR.3.4 alone the captured slot was a raw-int frame slot:
emit_call stored x's raw payload into k_3's slot 2 (offset 32) and
k_3's entry loaded back from that slot with `load.i64 v0+32`.

Under VR.4.3 the call chain (double + k_3) is native-callable end to
end: both leaf, both reached only at native Term::Call sites. use_x's
emit_call emits a native chain — call double → call k_3 with
(result, captured_x, host_ctx) — and k_3 itself is declared with the
`tail` calling convention, taking captured_x as a typed block param.
Captures no longer live in a heap frame at all, so `fz_alloc_frame`
for k_3's frame is gone entirely.
