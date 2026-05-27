---
purpose: "multi-clause dispatch with a guard clause (`when n > 0`), plus recursive `fact`"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 7
budget.codegen.instructions: 32
budget.specs.count: 7
budget.planner.worklist_pops: 18
budget.planner.walk_calls: 18
budget.planner.type_fn_calls: 7
budget.planner.matcher_specs: 0
budget.planner.vars: 53
budget.planner.blocks: 16
budget.planner.stmts: 27
budget.planner.dispatches: 6
---

# multi_clause

multi-clause dispatch with a guard clause (`when n > 0`), plus recursive `fact`
