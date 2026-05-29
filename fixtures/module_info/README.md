---
purpose: "__info__/1 reflection — a synthesized module fn reports functions, macros, and the module name on all four paths"
paths: [jit, interp, aot, repl]
---

# module_info

Every `defmodule` gains a synthesized `__info__/1` (fz-6df.12) built from its own
declarations. Because the synthesized body is pure literals, it lowers and runs
through the ordinary pipeline on all four paths with no backend special-casing.
Self-checked in-language:

```fz
assert(Shapes.__info__(:functions) == [{:area, 1}, {:perimeter, 1}], "exported fns with arities")
assert(Shapes.__info__(:macros) == [{:twice, 1}], "macros listed separately")
assert(Shapes.__info__(:module) == :Shapes, "module name as an atom")
assert(Shapes.__info__(:nonsense) == nil, "unknown kind yields nil")
```

`__info__` is an implicit reflection builtin: callable as `M.__info__`, but
excluded from the module interface, so `import M` does not sweep it in and it is
not subject to strict `@spec` validation.
