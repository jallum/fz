---
purpose: "selective receive with consecutive same-arity tuple clauses"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 18
budget.codegen.instructions: 403
budget.specs.count: 16
budget.planner.worklist_pops: 16
budget.planner.walk_calls: 16
budget.planner.type_fn_calls: 16
budget.planner.matcher_specs: 0
budget.planner.vars: 49
budget.planner.blocks: 16
budget.planner.stmts: 23
budget.planner.dispatches: 20
---

# receive_shared_tuple_arity

Selective receive whose clauses all inspect two-element tuples. This locks down
the shared tuple-schema matcher path used by receive matchers.
