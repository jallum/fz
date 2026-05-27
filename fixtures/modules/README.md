---
purpose: "cross-module qualified calls — `M.double`, `M.quad`, `N.helper`"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 2
budget.codegen.instructions: 15
budget.specs.count: 2
budget.planner.worklist_pops: 3
budget.planner.walk_calls: 3
budget.planner.type_fn_calls: 2
budget.planner.matcher_specs: 0
budget.planner.vars: 38
budget.planner.blocks: 5
budget.planner.stmts: 17
budget.planner.dispatches: 1
---

# modules

cross-module qualified calls — `M.double`, `M.quad`, `N.helper`
