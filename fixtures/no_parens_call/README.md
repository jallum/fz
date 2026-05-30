---
purpose: "no-parens calls (double 21; sum3 1, 2, 3) parse and run; output matches Elixir"
paths: [jit, interp, aot, repl]
oracle: oracle.exs
---

# no_parens_call

Exercises Elixir-style no-parens calls at statement position: `double 21` and
`sum3 1, 2, 3` are parsed as `double(21)` and `sum3(1, 2, 3)`. `oracle.exs` is
the Elixir twin (top-level fns become `M.double`/`M.sum3`); both print the same
integers, so `expected.txt` is owned by the oracle.
