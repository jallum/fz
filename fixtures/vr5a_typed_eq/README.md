---
purpose: "VR.5a — int-int / atom-atom equality lowers to a single icmp, no fz_value_eq dispatch"
paths: [jit, interp, repl]
---

# vr5a_typed_eq

VR.5a — int-int / atom-atom equality lowers to a single icmp, no fz_value_eq dispatch

## Notes

`1 == 2` and `:ok == :err`: ir_typer narrows both operands to int / atom
monomorphic Descrs. VR.5a's lower_eq fires the same-kind scalar arm:
tagged FzValues for a given scalar kind compare by bit equality, so the
emit is a single icmp eq + bool_to_fz. No both_ptr tag dispatch, no
fz_value_eq call site.
