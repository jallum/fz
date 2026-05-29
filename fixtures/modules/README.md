---
purpose: "cross-module qualified calls — `M.double`, `M.quad`, `N.helper`"
paths: [jit, interp, aot, repl]
---

# modules

Cross-module qualified calls (`M.double`, `M.quad`, `N.helper`), self-checked
in-language. The behavioural calls and the module structure are both asserted —
the latter via the synthesized `__info__/1` (fz-6df.12):

```fz
assert(M.double(21) == 42, "qualified call M.double")
assert(M.__info__(:functions) == [{:double, 1}, {:quad, 1}], "M exports double/1 and quad/1")
```
