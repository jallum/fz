---
purpose: "defmacro in one module, called from another via `import Helpers, only: [twice: 1]`"
paths: [jit, interp, aot, repl]
---

# cross_module_macro

`defmacro` in one module, called from another via `import Helpers, only:
[twice: 1]`. Self-checked in-language; `__info__` separates the module's macro
from its function:

```fz
assert(App.run(21) == 42, "imported macro twice/1 expands to Helpers.double and runs")
assert(Helpers.__info__(:macros) == [{:twice, 1}], "Helpers exposes the twice macro")
assert(Helpers.__info__(:functions) == [{:double, 1}], "Helpers exports double/1 as a function")
```
