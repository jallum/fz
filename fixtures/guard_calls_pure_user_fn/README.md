---
purpose: "case guards call pure user fns — locks X1A β-reduction three-path parity"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 12
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 14
budget.planner.blocks: 1
budget.planner.stmts: 10
budget.planner.dispatches: 0
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
