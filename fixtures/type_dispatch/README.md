---
purpose: multi-clause fn dispatches on parameter type at runtime (fz-ty1.8/1.9)
paths: [interp, jit, aot, repl]
---

# type_dispatch

`fn check(x :: integer)` emits a `TypeTest` guard that dispatches to the
integer clause for integer arguments and to the fallback clause for atoms.
Proves fz-ty1.8 (parser), fz-ty1.9 (lowering), and fz-ty1.6 (TypeTest codegen).
The guard lives in `check/1`, so the dispatch is exercised identically whether
the result is printed or asserted; the claim is self-checked in-language:

```fz
assert(check(42) == :is_int, "integer arg dispatches to the TypeTest clause")
assert(check(:foo) == :other, "atom arg falls through to the fallback clause")
```
