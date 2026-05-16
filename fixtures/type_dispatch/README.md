---
purpose: multi-clause fn dispatches on parameter type at runtime (fz-ty1.8/1.9)
paths: [interp, jit, aot]
---

`fn check(x :: integer)` emits a `TypeTest` guard that dispatches to the
integer clause for integer arguments and to the fallback clause for atoms.
Proves fz-ty1.8 (parser), fz-ty1.9 (lowering), and fz-ty1.6 (TypeTest codegen).
