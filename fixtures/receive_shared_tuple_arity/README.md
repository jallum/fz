---
purpose: "selective receive with consecutive same-arity tuple clauses"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 11
budget.codegen.instructions: 376
budget.specs.count: 9
budget.planner.worklist_pops: 20
budget.planner.walk_calls: 20
budget.planner.type_fn_calls: 9
budget.planner.matcher_specs: 0
budget.planner.vars: 57
budget.planner.blocks: 12
budget.planner.stmts: 31
budget.planner.dispatches: 4
---

# receive_shared_tuple_arity

Selective receive whose clauses all inspect two-element tuples. This locks down
the shared tuple-schema matcher path used by receive matchers.
