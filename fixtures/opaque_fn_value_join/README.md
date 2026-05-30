---
purpose: "opaque join of zero-capture function values remains callable through Enum.reduce/3"
paths: [jit, interp, aot, repl]
---

# opaque_fn_value_join

Pins the value-representation boundary for zero-capture function values after a
control-flow join. Both branches return a different named reducer, so the joined
value cannot be treated as one static reducer identity. Native execution must
still pass a closure-shaped value into the public reducer loop. The current
planner may specialize each branch target separately; the invariant is that the
joined callable value stays callable and does not force heap-continuation
materialization in the protocol-dispatched list reducer path.

This regressed when closure-call return-context facts were consumed directly in
codegen: the joined value reached the reducer loop as a scalar
word, and native execution panicked in `fz_closure_get_capture_ref`.
