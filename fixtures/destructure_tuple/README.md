---
purpose: "irrefutable tuple destructure in a let-style bind — first fixture to exercise `{a, b} = expr` across all four legs"
paths: [jit, interp, aot, repl]
---

# destructure_tuple

`{a, b} = pair()` — the simplest non-trivial destructure: irrefutable
tuple bind in expression position, on a value the typer can statically
prove is a 2-tuple. Pre-fz-fyq this either failed to compile under
warnings-as-errors (unreachable-arm noise on the synthesized fail
funnel) or compiled with a dead Halt(:match_error) block; this fixture
locks parity and silence across all four legs.
