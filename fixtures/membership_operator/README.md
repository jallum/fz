---
purpose: "membership operators desugar to Enum.member?/2 and match Elixir over List, Range, and Map"
paths: [jit, interp, aot, repl]
oracle: oracle.exs
---

Pins the Elixir-facing `in` / `not in` surface. The parser keeps these as
operators long enough to preserve precedence; compiler2 source production
normalizes them to `Enum.member?/2` before function-source lowering.
