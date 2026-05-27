---
purpose: "minimal call site — one fn definition, one call, no scaffolding"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 8
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 9
budget.planner.blocks: 2
budget.planner.stmts: 5
budget.planner.dispatches: 0
---

# cold_fn

minimal call site — one fn definition, one call, no scaffolding
