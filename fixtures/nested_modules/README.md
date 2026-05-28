---
purpose: "inner module addressed both fully-qualified (`Outer.Inner.f`) and via outer-local reference"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 13
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 18
budget.planner.blocks: 1
budget.planner.stmts: 10
budget.planner.dispatches: 0
---

# nested_modules

inner module addressed both fully-qualified (`Outer.Inner.f`) and via outer-local reference
