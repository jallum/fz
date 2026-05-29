---
purpose: "multi-clause dispatch with a guard clause (`when n > 0`), plus recursive `fact`"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 4
budget.codegen.instructions: 22
budget.specs.count: 4
budget.planner.worklist_pops: 9
budget.planner.walk_calls: 9
budget.planner.type_fn_calls: 4
budget.planner.matcher_specs: 0
budget.planner.vars: 42
budget.planner.blocks: 9
budget.planner.stmts: 23
budget.planner.dispatches: 3
---

# multi_clause

multi-clause dispatch with a guard clause (`when n > 0`), plus recursive `fact`
