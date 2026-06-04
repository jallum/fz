---
purpose: "smallest JIT round-trip — fn def + call + print"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 7
budget.specs.count: 3
budget.planner.worklist_pops: 3
budget.planner.walk_calls: 3
budget.planner.type_fn_calls: 3
budget.planner.matcher_specs: 0
budget.planner.vars: 8
budget.planner.blocks: 3
budget.planner.stmts: 4
budget.planner.dispatches: 2
---
