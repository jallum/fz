---
purpose: "pipe macro rewrite for call RHS and headless case RHS"
paths: [jit, interp, aot]
---

# pipe_headless_case

Exercises `lhs |> f(args)` and `lhs |> case do ... end` after pipe handling
moved into macro expansion.
