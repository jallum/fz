---
purpose: "same call repeated — historical JIT tier-up trigger; today every call is JIT"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 23
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 61
budget.planner.blocks: 1
budget.planner.stmts: 40
budget.planner.dispatches: 0
---

# hot_fn

same call repeated — historical JIT tier-up trigger; today every call is JIT
