---
purpose: "VR.1 — int-literal arithmetic elides the tag-check fast/slow path"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 2
budget.codegen.instructions: 15
budget.specs.count: 2
budget.planner.worklist_pops: 3
budget.planner.walk_calls: 3
budget.planner.type_fn_calls: 2
budget.planner.matcher_specs: 0
budget.planner.vars: 30
budget.planner.blocks: 5
budget.planner.stmts: 15
budget.planner.dispatches: 1
---

# vr1_int_arith

VR.1 — int-literal arithmetic elides the tag-check fast/slow path

## Notes

(icmp_imm eq + bxor_imm are signatures of the elided tag-check scaffold.
 brif appears unrelatedly for the cont-ptr null check at fn exit, so we
 don't exclude it.)

Both operands of each op are Int literals → ir_planner narrows to int →
lower_prim's descr_is_int gate fires → the bxor/icmp/brif tag-check
scaffold around fz_arith_add is elided. We still see the unbox/iadd/rebox
inline (raw add on the tagged-int payload), but no dispatch test.
Closing the boxing gap is VR.3 (raw frame slots) and VR.4 (typed ABI).
