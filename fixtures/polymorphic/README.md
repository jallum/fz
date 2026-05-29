---
purpose: "parametric `id` exercised over int, atom, and bool"
paths: [jit, interp, aot, repl]
---

# polymorphic

Parametric `id` exercised over int, atom, and bool, self-checked in-language:

```fz
assert(id(42) == 42, "id on int")
assert(id(:hello) == :hello, "id on atom")
assert(id(true), "id on bool")
```
