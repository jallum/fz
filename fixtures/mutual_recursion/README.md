---
purpose: "mutual recursion — is_even/is_odd call each other; exercises cross-function recursive dispatch"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 4
budget.codegen.instructions: 31
budget.specs.count: 4
budget.planner.worklist_pops: 9
budget.planner.walk_calls: 9
budget.planner.type_fn_calls: 4
budget.planner.matcher_specs: 0
budget.planner.vars: 28
budget.planner.blocks: 8
budget.planner.stmts: 16
budget.planner.dispatches: 3
---

# mutual_recursion

mutual recursion — is_even/is_odd call each other; exercises cross-function recursive dispatch
