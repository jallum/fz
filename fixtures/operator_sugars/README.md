---
purpose: "operator desugaring rewrites ++, --, <>, .., and ..// to runtime-library calls"
paths: [jit, interp, aot, repl, fz2-run, fz2-interp, fz2-build]
oracle: oracle.exs
---

Exercises the user-facing operator spellings after compiler2 source-sugar
normalization. List operators become source `List` helper calls, binary
concatenation becomes the Kernel primitive wrapper call, and range literals
construct the source `Range` struct.
