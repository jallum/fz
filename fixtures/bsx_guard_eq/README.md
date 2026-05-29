---
purpose: "fz-bsx.4 — a guard comparison (when s == \"hi\") on a utf8 binding is brand-blind on all paths"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 5
budget.codegen.instructions: 120
budget.specs.count: 5
budget.planner.worklist_pops: 7
budget.planner.walk_calls: 7
budget.planner.type_fn_calls: 5
budget.planner.matcher_specs: 0
budget.planner.vars: 40
budget.planner.blocks: 12
budget.planner.stmts: 25
budget.planner.dispatches: 4
---

# bsx_guard_eq

Regression guard for fz-bsx: a `when s == "hi"` guard where `s` is bound to a
`utf8` value must fire (`:guard_hit`) on every path. Guard `==` lowers to the
same brand-blind equality fold as a top-level `==`.
