---
purpose: "sequential calls returning tuple-pattern results (fz-i82 regression)"
paths: [interp, jit, aot, repl]
---

# case_tuple_pattern_sequential

Regression lock for fz-i82. Two helpers — one `case`-based, one `with`-based —
each with a tuple-pattern arm and an atom-literal fallback. `main` calls them in
both orders so every callsite return flows into another call's argument (now the
`==` of an assert), exercising the cont-chain seam where the bug lived.

The bug: codegen had a per-spec return-Descr fixpoint that ignored
`reachable_blocks` and didn't propagate through `Call`+continuation, disagreeing
with `module_types.effective_returns`. The `:err` arm's narrow `0` return got
tag-boxed into raw bits `1`. fz-i82.2 deleted the duplicate fixpoint; codegen
now reads `effective_returns` directly. The assertion catches the regression
directly: a mis-boxed `0` makes `f(:err) == 0` false and aborts.

```fz
assert(f(:err) == 0, "case atom fallback returns 0")
```
