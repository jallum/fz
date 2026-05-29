---
purpose: "first-class fns — pass a fn into another fn and call it"
paths: [jit, interp, aot, repl]
---

# apply2

First-class functions — pass a fn into another fn and call it, self-checked
in-language:

```fz
assert(apply2(double, 21) == 42, "apply2 calls a passed fn")
```
