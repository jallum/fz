---
purpose: "fibonacci via two-accumulator tail recursion — three-clause dispatch + tail-call forwarding under load"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 4
budget.codegen.instructions: 23
budget.specs.count: 4
budget.planner.worklist_pops: 9
budget.planner.walk_calls: 9
budget.planner.type_fn_calls: 4
budget.planner.matcher_specs: 0
budget.planner.vars: 36
budget.planner.blocks: 8
budget.planner.stmts: 24
budget.planner.dispatches: 3
---

# fib_tailrec

fibonacci via two-accumulator tail recursion — three-clause dispatch + tail-call forwarding under load
