---
purpose: "Map implements Enumerable reduce/count/member?/slice callbacks"
paths: [jit, interp, aot, repl]
oracle: oracle.exs
---

Exercises the source `defimpl Enumerable, for: Map` callback surface through
direct protocol calls. The oracle uses Elixir maps and `Enumerable.Map`, so the
checked output pins callback semantics and canonical map iteration order.
