---
purpose: "defmacro + quote/unquote round-trip — two macros, one nested in the other"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 9
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 18
budget.planner.blocks: 1
budget.planner.stmts: 14
budget.planner.dispatches: 0
---

# macro_inc

defmacro + quote/unquote round-trip — two macros, one nested in the other
