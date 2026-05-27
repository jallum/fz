---
purpose: "fibonacci via two-accumulator tail recursion — three-clause dispatch + tail-call forwarding under load"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 18
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 25
budget.planner.blocks: 1
budget.planner.stmts: 20
budget.planner.dispatches: 0
---

# fib_tailrec

fibonacci via two-accumulator tail recursion — three-clause dispatch + tail-call forwarding under load
