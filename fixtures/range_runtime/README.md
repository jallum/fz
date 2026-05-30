---
purpose: "Range runtime constructor prints Elixir-style range literals"
paths: [jit, interp, aot, repl]
oracle: oracle.exs
---

Exercises the runtime Range constructor exposed through `Kernel.range/3`.
The oracle uses Elixir range literals so fixture output proves the rendered
form, including explicit non-default steps, matches Elixir.
