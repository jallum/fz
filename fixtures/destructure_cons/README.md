---
purpose: "refutable list-cons destructure on a statically-non-empty list — success-path parity for `[h | t] = xs`"
paths: [jit, interp, aot, repl]
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
