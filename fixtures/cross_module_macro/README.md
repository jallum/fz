---
purpose: "defmacro in one module, called from another via `import Helpers, only: [twice: 1]`"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 5
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 8
budget.planner.blocks: 1
budget.planner.stmts: 4
budget.planner.dispatches: 0
---

# cross_module_macro

defmacro in one module, called from another via `import Helpers, only: [twice: 1]`
