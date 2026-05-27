---
purpose: "refutable list-cons destructure on a statically-non-empty list — success-path parity for `[h | t] = xs`"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 13
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 13
budget.planner.blocks: 2
budget.planner.stmts: 9
budget.planner.dispatches: 0
---

# destructure_cons

`[h | t] = [10, 20, 30]` — list-cons destructure in a let-style bind.
Structurally refutable (the bind would crash with `:match_error` on
the empty list), but here the scrutinee is a literal non-empty list,
so the planner proves the empty-list edge dead and `ir_branch_fold`
elides it.

The mismatch case (`[h | t] = []` → runtime `:match_error`) is BEAM-
conform but not parity-tested via the matrix, which only asserts
`exit 0` outcomes. That contract is verified by hand and locked in
ad-hoc tests under `src/`.
