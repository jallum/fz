---
purpose: "higher-order patterns — apply2, compose"
paths: [jit, interp, aot, repl]
---

# higher_order

Higher-order patterns — `apply2` and `compose` over first-class functions,
self-checked in-language:

```fz
assert(apply2(double, 21) == 42, "apply2 calls a passed fn")
assert(compose(double, neg, 5) == -10, "compose chains two fns")
```
