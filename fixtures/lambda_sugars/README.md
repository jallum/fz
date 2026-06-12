---
purpose: "capture shorthand and multi-clause anonymous fn desugar to ordinary lambda dispatch"
paths: [jit, interp, aot, repl, fz2-run, fz2-interp, fz2-build]
oracle: oracle.exs
---

# lambda_sugars

Exercises the fz-g58.15 lambda desugar surface. Capture shorthand becomes an
ordinary lambda, and guarded multi-clause anonymous functions dispatch through
the same pattern machinery as `case`.
