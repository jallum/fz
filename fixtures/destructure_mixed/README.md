---
purpose: "nested destructure mixing tuple arity and list cons — `{[h | t], y} = make()` across all four legs"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 2
budget.codegen.instructions: 37
budget.specs.count: 3
budget.typer.worklist_pops: 4
budget.typer.walk_calls: 4
budget.typer.type_fn_calls: 3
budget.typer.matcher_specs: 0
budget.typer.vars: 51
budget.typer.blocks: 11
budget.typer.stmts: 23
budget.typer.dispatches: 2
---

# destructure_mixed

`{[h | t], y} = make()` — nested destructure binding through a tuple
into a list-cons in one leg of the tuple. Stresses the matrix
helpers' recursion (tuple specialization → list-cons specialization)
and confirms `BranchOrigin::PatternBind` propagates across both
levels so the diagnostic stays silent end-to-end.
