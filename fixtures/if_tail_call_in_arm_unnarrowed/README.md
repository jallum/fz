---
purpose: "fz-84m repro C — same shape as repro B but with `n > 0` instead of `n == 0`, proving the bug was structural in lowering and NOT driven by per-callsite type narrowing"
paths: [jit, interp]
---

# if_tail_call_in_arm_unnarrowed

fz-84m repro C — repro B's structure without the type narrowing.

## History

While diagnosing fz-84m we initially attributed the bug to typer
narrowing (per-callsite specialization producing `none`-typed arms).
This repro proves otherwise: with `n > 0` (a relational predicate,
not an equality on a singleton), the typer doesn't narrow `pick`'s
arms — yet pre-fz-duq.2 the bug fires identically.

The root was `lower_if` unconditionally overwriting tail-terminated
arms (Bug 1) and using block-level joins that couldn't survive a
CPS-split inside an arm (Bug 2). Both are structural to the
lowering pass — nothing to do with the type system.

Expected stdout:

```
7
99
```
