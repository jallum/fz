---
purpose: VR.5b — print dispatches to typed FFI when the arg Descr narrows
paths: [jit, interp]
expect_clif_excludes:
  - fn: int_main
    substr: fz_print_value
  - fn: float_main
    substr: fz_print_value
---

# vr5b_typed_print

VR.5b — print dispatches to typed FFI when the arg Descr narrows

## Notes

Before fz-ul4.27.7, every `print(x)` went through `fz_print_value(boxed)`
— for typed args this required tagging up the raw value before the call.
After .5b, lower_prim's Print branch checks `descr_is_int` /
`descr_is_float` and routes to `fz_print_i64` (i64) / `fz_print_f64`
(f64) directly, skipping the box. The typed helpers render identically
to fz_print_value's render() output (4.0 stays "4.0", not "4") and
push to TEST_CAPTURE so cargo-test assertions keep working through
either entry point.

Polymorphic prints (arg type `any`) still route through fz_print_value
— VR.5b doesn't lose the fallback; it just adds two fast paths.
