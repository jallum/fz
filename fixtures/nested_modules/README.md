---
purpose: "inner module addressed both fully-qualified (`Outer.Inner.f`) and via outer-local reference"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 3
budget.codegen.instructions: 18
budget.specs.count: 3
budget.planner.worklist_pops: 6
budget.planner.walk_calls: 6
budget.planner.type_fn_calls: 3
budget.planner.matcher_specs: 0
budget.planner.vars: 26
budget.planner.blocks: 6
budget.planner.stmts: 13
budget.planner.dispatches: 2
---

# nested_modules

inner module addressed both fully-qualified (`Outer.Inner.f`) and via outer-local reference
