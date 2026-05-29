---
purpose: "first-match-wins for wildcard-then-specific patterns (multi-clause fn and case)"
paths: [jit, interp, aot, repl]
---

# wildcard_then_specific

Locks in **first-match-wins** semantics when a wildcard precedes a more
specific pattern. With Maranget-style matrix specialization (fz-ul4.43.D.1+),
naive specialization can re-order sub-matrices to put the specific row
first, silently changing which clause fires. Source order is preserved by
sorting sub-matrix rows by body_id at every specialization step
(fz-ul4.45).

Both clause shapes — multi-clause `fn` (catch) and `case` (cmatch) — must
dispatch every input to the wildcard clause. The second clauses (`:zero` for
input `0`) are dead code, never reached. The invariant is asserted in-language
on every path:

```fz
assert(catch(0) == :anything, "fn: wildcard precedes specific, first-match-wins")
assert(cmatch(0) == :anything, "case: wildcard precedes specific, first-match-wins")
```

Acceptance: every call yields `:anything`; no input ever produces `:zero`.
