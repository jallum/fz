---
purpose: "case guards call pure user fns — locks X1A β-reduction three-path parity"
paths: [jit, interp, aot, repl]
---

# guard_calls_pure_user_fn

Case guards call pure user fns — locks X1A β-reduction three-path parity.
Self-checked in-language:

```fz
assert(classify(5) == :pos, "guard calling a pure user fn fires")
assert(classify(0) == :other, "0 falls through both guards")
```
