---
purpose: "fz-bsx.4 — a guard comparison (when s == \"hi\") on a utf8 binding is brand-blind on all paths"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 11
budget.codegen.instructions: 137
budget.specs.count: 11
budget.planner.worklist_pops: 11
budget.planner.walk_calls: 11
budget.planner.type_fn_calls: 11
budget.planner.matcher_specs: 0
budget.planner.vars: 35
budget.planner.blocks: 19
budget.planner.stmts: 23
budget.planner.dispatches: 11
---

# bsx_guard_eq

Regression guard for fz-bsx: a `when s == "hi"` guard where `s` is bound to a
`utf8` value must fire (`:guard_hit`) on every path. Guard `==` lowers to the
same brand-blind equality fold as a top-level `==`.
