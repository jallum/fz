---
purpose: "VR.4 + VR.3.2 + .27.13 — narrow-spec float entry params arrive in F64 registers; fmul/fadd fire raw"
paths: [jit, interp]
expect_clif_contains:
  - fn: dist
    substr: "block0(v0: f64, v1: f64, v2: i64)"
  - fn: dist
    substr: fmul
  - fn: dist
    substr: fadd
expect_clif_excludes:
  - fn: dist
    substr: load.f64
---

# vr3_float_args

VR.4 + VR.3.2 + .27.13 — narrow-spec float entry params arrive in F64 registers; fmul/fadd fire raw

## Notes

fz-ul4.27.10 call-site narrowing types x, y as float (caller passes
1.5, 2.5). Under .27.13 the narrow `dist_s3` spec promotes those param
slots to F64 in the Cranelift signature; entry block_params carry f64
directly, no frame slot is involved, and no `load.f64` is emitted
anywhere in the body. fmul/fadd fire on the raw register values; the
return rides back as f64 to the (also-narrowed) cont. Caller's
`f64const 1.5` / `f64const 2.5` flow straight to the call.
fz-cps.1.a (fz-siu.1.1): trailing v2:i64 is the cont parameter per
docs/cps-in-clif.md §2.1; threaded but unused in .1.1.
