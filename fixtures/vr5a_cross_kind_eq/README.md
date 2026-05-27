---
purpose: "VR.5a — cross-kind `==` folds to constant + emits type/dead-binop lint"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 8
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 6
budget.planner.blocks: 1
budget.planner.stmts: 4
budget.planner.dispatches: 0
---

# vr5a_cross_kind_eq

VR.5a — cross-kind `==` folds to constant + emits type/dead-binop lint

## Notes

(icmp eq is NOT excluded — the continuation null-check at fn exit
 emits one unrelated to the folded comparison.)

`1 == :ok` has empty intersection in the planner (int axis vs atom axis,
no shared kind). VR.5a folds the comparison to FALSE_BITS at codegen
and ir_planner surfaces a type/dead-binop warning. Neq would fold to
TRUE_BITS — both routes through the same disjointness check.

FALSE_BITS encodes as i64 immediate 19 ((2<<3)|0b011, see TAG_BOOL +
false_id in src/ir_codegen.rs); `iconst.i64 19` is the codegen
signature for the fold. We exclude icmp eq because no comparison
instruction should reach the emit.
