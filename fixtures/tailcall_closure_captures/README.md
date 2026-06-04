---
purpose: "TailCallClosure with captured singleton closure-lit preserves narrow arg ABI through recursive HOF"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 8
budget.codegen.instructions: 122
budget.specs.count: 8
budget.planner.worklist_pops: 8
budget.planner.walk_calls: 8
budget.planner.type_fn_calls: 8
budget.planner.matcher_specs: 0
budget.planner.vars: 40
budget.planner.blocks: 15
budget.planner.stmts: 19
budget.planner.dispatches: 7
---

# tailcall_closure_captures

Recursive higher-order call through a captured closure-lit must pass the
list element to the lambda body in the lambda's narrow representation.
