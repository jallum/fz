---
purpose: "opaque join of zero-capture function values remains callable through Enum.reduce/3"
paths: [jit, interp, aot, repl]
---

# opaque_fn_value_join

Pins the value-representation boundary for zero-capture function values after a
control-flow join. Both branches return a different named reducer, so the joined
value cannot be treated as one static reducer identity. Native execution must
still pass a closure-shaped value to the indirect reducer call.

This regressed when closure-call return-context facts were consumed directly in
codegen: the joined value reached `Enumerable.reduce_list_cont/3` as a scalar
word, and native execution panicked in `fz_closure_get_capture_ref`.
