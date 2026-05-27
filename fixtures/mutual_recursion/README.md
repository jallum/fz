---
purpose: "mutual recursion — is_even/is_odd call each other; exercises cross-function recursive dispatch"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 15
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 17
budget.planner.blocks: 1
budget.planner.stmts: 12
budget.planner.dispatches: 0
---

# mutual_recursion

mutual recursion — is_even/is_odd call each other; exercises cross-function recursive dispatch
