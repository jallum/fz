---
purpose: "TailCallClosure with captured singleton closure-lit preserves narrow arg ABI through recursive HOF"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 6
budget.codegen.instructions: 93
budget.specs.count: 6
budget.planner.worklist_pops: 13
budget.planner.walk_calls: 13
budget.planner.type_fn_calls: 6
budget.planner.matcher_specs: 0
budget.planner.vars: 39
budget.planner.blocks: 11
budget.planner.stmts: 19
budget.planner.dispatches: 6
---

# tailcall_closure_captures

Recursive higher-order call through a captured closure-lit must pass the
list element to the lambda body in the lambda's narrow representation.
