---
purpose: "operator desugaring rewrites ++, --, <>, .., and ..// to runtime-library calls"
paths: [jit, interp, aot, repl]
oracle: oracle.exs
---

Exercises the user-facing operator spellings after the macro/desugar pass. List
operators lower to source `List` helpers, binary concatenation lowers to the
Kernel primitive wrapper, and range literals construct the source `Range`
struct.
