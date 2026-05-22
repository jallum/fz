---
purpose: "selective receive with consecutive same-arity tuple clauses"
paths: [jit, interp, aot]
budget.codegen.functions: 18
budget.codegen.instructions: 519
budget.specs.count: 19
---

# receive_shared_tuple_arity

Selective receive whose clauses all inspect two-element tuples. This locks down
the shared tuple-schema matcher path used by receive matchers.
