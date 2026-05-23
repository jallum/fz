---
purpose: "first-match-wins for wildcard-then-specific patterns (multi-clause fn and case)"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 3
budget.codegen.instructions: 44
budget.specs.count: 3
budget.typer.worklist_pops: 6
budget.typer.walk_calls: 6
budget.typer.type_fn_calls: 3
budget.typer.matcher_specs: 0
budget.typer.vars: 41
budget.typer.blocks: 7
budget.typer.stmts: 16
budget.typer.dispatches: 2
---

# wildcard_then_specific

Locks in **first-match-wins** semantics when a wildcard precedes a more
specific pattern. With Maranget-style matrix specialization (fz-ul4.43.D.1+),
naive specialization can re-order sub-matrices to put the specific row
first, silently changing which clause fires. Source order is preserved by
sorting sub-matrix rows by body_id at every specialization step
(fz-ul4.45).

Both clause shapes — multi-clause `fn` (catch) and `case` (cmatch) —
must dispatch every input to the wildcard clause. The second clauses
(`:zero` for input `0`) are dead code, never reached.

Acceptance: every call prints `:anything`; no input ever produces `:zero`.
