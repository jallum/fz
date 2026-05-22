---
purpose: "selective receive with consecutive same-arity tuple clauses"
paths: [jit, interp, aot]
budget.codegen.min_functions: 18
budget.codegen.max_functions: 18
budget.codegen.min_instructions: 415
budget.codegen.max_instructions: 623
budget.specs.min_count: 15
budget.specs.max_count: 23
---

# receive_shared_tuple_arity

Selective receive whose clauses all inspect two-element tuples. This locks down
the shared tuple-schema matcher path used by receive matchers.
