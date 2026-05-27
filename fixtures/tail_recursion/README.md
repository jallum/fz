---
purpose: "100k-deep self-recursion must TCO — exits cleanly with the accumulated count"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 3
budget.codegen.instructions: 28
budget.specs.count: 3
budget.planner.worklist_pops: 6
budget.planner.walk_calls: 6
budget.planner.type_fn_calls: 3
budget.planner.matcher_specs: 0
budget.planner.vars: 17
budget.planner.blocks: 6
budget.planner.stmts: 10
budget.planner.dispatches: 3
---

# tail_recursion

100k-deep self-recursion must TCO — exits cleanly with the accumulated count
