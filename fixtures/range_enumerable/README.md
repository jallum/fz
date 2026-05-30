---
purpose: "Range implements Enumerable reduce/count/member?/slice callbacks"
paths: [jit, interp, aot, repl]
oracle: oracle.exs
---

Exercises the source `defimpl Enumerable, for: Range` callback surface through
direct protocol calls. The oracle uses Elixir range literals and
`Enumerable.Range`, so the checked output pins callback semantics rather than
Range rendering alone.
