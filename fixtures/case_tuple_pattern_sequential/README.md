---
purpose: "sequential calls returning tuple-pattern results (fz-i82 regression)"
paths: [interp]
---

# case_tuple_pattern_sequential

Regression lock for fz-i82. Two helpers — one `case`-based, one
`with`-based — each with a tuple-pattern arm and an atom-literal
fallback. `main` calls them in both orders so every callsite return
flows into another callsite's argument, exercising the cont-chain
seam that the bug lived on.

## fz-i82.2 promotes this to `jit + aot`

Today only the `interp` path is correct: codegen's per-spec return-
Descr fixpoint disagrees with the typer's `effective_returns`, so
the narrow `0` return of the `:err` arm gets tag-boxed and the cont
reads `1`. fz-i82.2 deletes the duplicate fixpoint and reblesses
the goldens; this fixture's frontmatter flips to
`paths: [interp, jit, aot]` in that commit.
