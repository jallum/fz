---
purpose: "refutable list-cons destructure on a statically-non-empty list — success-path parity for `[h | t] = xs`"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 68
budget.specs.count: 1
budget.typer.worklist_pops: 1
budget.typer.walk_calls: 1
budget.typer.type_fn_calls: 1
budget.typer.matcher_specs: 0
budget.typer.vars: 21
budget.typer.blocks: 5
budget.typer.stmts: 12
budget.typer.dispatches: 0
---

# destructure_cons

`[h | t] = [10, 20, 30]` — list-cons destructure in a let-style bind.
Structurally refutable (the bind would crash with `:match_error` on
the empty list), but here the scrutinee is a literal non-empty list,
so the typer proves the empty-list edge dead and `ir_branch_fold`
elides it.

The mismatch case (`[h | t] = []` → runtime `:match_error`) is BEAM-
conform but not parity-tested via the matrix, which only asserts
`exit 0` outcomes. That contract is verified by hand and locked in
ad-hoc tests under `src/`.
