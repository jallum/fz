---
purpose: VR.3.3 / VR.4.2.3 — typed int args flow through native ABI
paths: [jit, interp]
expect_clif_contains:
  - fn: sum3
    substr: iadd
  - fn: sum3
    substr: tail
expect_clif_excludes:
  - fn: sum3
    substr: fz_alloc_frame
---

# vr3_int_args

VR.3.3 / VR.4.2.3 — typed int args flow through native ABI

## Notes

fz-cps.1.12: load.i64 in sum3 is now from `Term::Return`'s indirect-call
(load cont+16) per docs/cps-in-clif.md §2.1. The pre-cps assertion that
sum3 has zero loads is obsolete; the body's lack of entry-frame loads
is the new invariant. Keeping iadd/tail/fz_alloc_frame-excluded checks.

fz-ul4.27.10 call-site narrowing types a, b, c as int (caller passes
int literals). Under VR.3.3 alone the entry-frame slots were marked
FieldKind::RawI64 and codegen loaded raw i64 directly, skipping the
per-op sshr round trip.

Under VR.4.2.3 sum3 itself becomes natively-callable (body-leaf, not
a continuation, not main, reached by direct Term::Call from main).
The entry frame disappears entirely — args arrive via block params
on the typed `(i64, i64, i64, i64) -> i64 tail` native sig, the body
sshrs each tagged arg once, then iadds. The wins are:
  * no `load.i64` (no entry frame at all)
  * no `fz_alloc_frame` at the caller's call site (the previous frame
    allocation was the dominant per-call overhead)
  * `tail` calling convention enables future return_call TCO
