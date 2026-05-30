---
purpose: "defstruct-backed Range values print Elixir-style range literals"
paths: [jit, interp, aot, repl]
oracle: oracle.exs
---

Exercises `Range.new/3` and `Kernel.range/3`, both backed by the source
`defstruct` surface. The oracle uses Elixir range literals so fixture output
proves field access and rendering, including explicit non-default steps, match
Elixir.
