---
purpose: "selective import — `import Math, only: [add: 2]`"
paths: [jit, interp, aot, repl]
---

# import

Selective import (`import Math, only: [add: 2]`). The imported call works, and
`__info__` proves import does not re-export — `User.__info__(:functions)` lists
only `calc/2`, not the imported `add`:

```fz
assert(User.calc(10, 32) == 42, "imported add/2 used inside calc")
assert(User.__info__(:functions) == [{:calc, 2}], "import does not re-export")
```
