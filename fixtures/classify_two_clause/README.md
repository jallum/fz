---
purpose: "literal-vs-wildcard clause dispatch (`0` and `_`)"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 2
budget.codegen.instructions: 10
budget.specs.count: 2
budget.planner.worklist_pops: 3
budget.planner.walk_calls: 3
budget.planner.type_fn_calls: 2
budget.planner.matcher_specs: 0
budget.planner.vars: 20
budget.planner.blocks: 4
budget.planner.stmts: 10
budget.planner.dispatches: 1
---

# classify_two_clause

literal-vs-wildcard clause dispatch (`0` and `_`)
