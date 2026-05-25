---
purpose: "selective receive with consecutive same-arity tuple clauses"
paths: [jit, interp, aot]
budget.codegen.functions: 11
budget.codegen.instructions: 376
budget.specs.count: 9
budget.typer.worklist_pops: 20
budget.typer.walk_calls: 20
budget.typer.type_fn_calls: 9
budget.typer.matcher_specs: 0
budget.typer.vars: 57
budget.typer.blocks: 12
budget.typer.stmts: 31
budget.typer.dispatches: 4
---

# receive_shared_tuple_arity

Selective receive whose clauses all inspect two-element tuples. This locks down
the shared tuple-schema matcher path used by receive matchers.
