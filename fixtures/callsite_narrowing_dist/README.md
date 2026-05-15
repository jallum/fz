---
purpose: "fz-ul4.27.10 — call-site arg narrowing flows caller arg types into callee entry params"
paths: [jit, interp]
expect_clif_contains:
  - fn: dist
    substr: fadd
  - fn: dist
    substr: fmul
expect_clif_excludes:
  - fn: dist
    substr: fz_arith_add
  - fn: dist
    substr: fz_arith_mul
---

# callsite_narrowing_dist

fz-ul4.27.10 — call-site arg narrowing flows caller arg types into callee entry params

## Notes

Before fz-ul4.27.10, ir_typer left every entry-block param at `any`, so
`dist`'s x and y were polymorphic and `x * x + y * y` lowered through
fz_arith_mul / fz_arith_add. After .27.10, type_module iterates to a
fixed point and propagates main's call-site arg types (float-float) into
dist's entry params. The existing VR.2 float fast paths then fire and
the body lowers to native fmul + fadd, with no dispatch helpers in
sight.
