---
purpose: "irrefutable tuple destructure in a let-style bind — first fixture to exercise `{a, b} = expr` across all four legs"
paths: [jit, interp, aot, repl]
---

# destructure_tuple

`{a, b} = pair()` — the simplest non-trivial destructure: irrefutable tuple
bind in expression position, on a value the planner can statically prove is a
2-tuple. Pre-fz-fyq this either failed to compile under warnings-as-errors
(unreachable-arm noise on the synthesized fail funnel) or compiled with a dead
`Halt(:match_error)` block; this fixture locks parity and silence across all
four legs, now via in-language assertions:

```fz
{a, b} = pair()
assert(a == 1, "first tuple element binds")
assert(b == 2, "second tuple element binds")
```
