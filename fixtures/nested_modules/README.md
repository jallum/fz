---
purpose: "inner module addressed both fully-qualified (`Outer.Inner.f`) and via outer-local reference"
paths: [jit, interp, aot, repl]
---

# nested_modules

Inner module addressed both fully-qualified (`Outer.Inner.f`) and via an
outer-local reference (`Inner.f` inside `Outer`). Self-checked in-language,
including the structure via `__info__`:

```fz
assert(Outer.Inner.f(7) == 1007, "fully-qualified inner f")
assert(Outer.__info__(:functions) == [{:f, 1}, {:use_inner, 1}], "outer exports its own fns, not the nested module")
```
