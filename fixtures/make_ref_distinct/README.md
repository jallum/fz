---
purpose: "fz-ht5 — make_ref() returns a distinct opaque ref on every call"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 20
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 12
budget.planner.blocks: 3
budget.planner.stmts: 6
budget.planner.dispatches: 0
---

# make_ref_distinct

fz-ht5 — Two successive calls to `make_ref()` must return distinct values. The
value's type is the opaque `ref`; arithmetic on it is rejected by the planner
(separate fixture / negative test).
