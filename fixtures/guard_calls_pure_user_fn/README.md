---
purpose: "case guards call pure user fns — locks X1A β-reduction three-path parity"
paths: [jit, interp, aot]
budget.codegen.functions: 3
budget.codegen.instructions: 40
budget.specs.count: 3
budget.typer.worklist_pops: 6
budget.typer.walk_calls: 6
budget.typer.type_fn_calls: 3
budget.typer.matcher_specs: 0
budget.typer.vars: 22
budget.typer.blocks: 6
budget.typer.stmts: 13
budget.typer.dispatches: 2
---

# guard_calls_pure_user_fn

fz-puj.49 (X1A) — pure user-fn inline-substitution in guards.

Two pure user fns (`is_pos`, `double`) are called from inside a case
guard. Pre-X1A this would have triggered a clean
`LowerError::Unsupported` (the fz-puj.42 diagnostic). With X1A,
`inline_pure_user_fn_calls_in_guard` β-reduces each Call at lower time
so the guard becomes a pure-Expr predicate that the matcher fn can host
without a CPS-split.

Nested calls inline too (`is_pos(double(x))` → `is_pos(x * 2)` → `x * 2 > 0`).
