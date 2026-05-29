---
purpose: "@moduledoc / @doc attributes parse and the module still executes"
paths: [jit, interp, aot, repl]
---

# attributes

`@moduledoc` / `@doc` attributes parse and the module still executes. Self-checked
in-language; `__info__` confirms the attributes don't disturb the module's
exports:

```fz
assert(Greeter.hi(:alice) == :alice, "module with @moduledoc/@doc still executes")
assert(Greeter.__info__(:functions) == [{:hi, 1}, {:echo, 1}], "@doc/@moduledoc do not disturb the exports")
```
