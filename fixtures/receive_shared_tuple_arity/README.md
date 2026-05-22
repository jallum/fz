---
purpose: "selective receive with consecutive same-arity tuple clauses"
paths: [jit, interp, aot]
budget.codegen.functions: 18
budget.codegen.instructions: 519
budget.specs.count: 8
budget.typer.worklist_pops: 15
budget.typer.walk_calls: 15
budget.typer.type_fn_calls: 8
budget.typer.matcher_specs: 0
budget.typer.vars: 58
budget.typer.blocks: 11
budget.typer.stmts: 31
budget.typer.dispatches: 1
---

# receive_shared_tuple_arity

Selective receive whose clauses all inspect two-element tuples. This locks down
the shared tuple-schema matcher path used by receive matchers.
