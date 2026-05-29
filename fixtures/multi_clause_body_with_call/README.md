---
purpose: "minimal multi-clause Bug-2 repro — clause body has a Call. Pre-fz-qbg.2 panicked at fz_ir.rs:453; now lowers correctly via the per-clause body cont-fn path"
paths: [jit, interp, aot, repl]
---

# multi_clause_body_with_call

Minimal repro for the multi-clause class of Bug-2 (fz-g8v) — fz-qbg.2's
test case in fixture form. The clause body `helper()` is still a Call inside
`classify/1`, so the per-clause cont-fn lowering path is exercised exactly as
before; only the top-level check moved from `dbg` to `assert`.

## History

Pre-fz-qbg.2: `classify(0)`'s body `helper()` is a tail-position Call, but the
`helper()` lowering as `lower_expr(_, is_tail=true)` doesn't CPS-split for
top-level calls. `body_might_cps_split` flags the call shape as worth wrapping;
with fz-qbg.2 it wraps, the clause body lives in `fn_clause_0`, and
`TailCall(helper)` becomes the cont fn's terminator.

```fz
assert(classify(0) == 7, "clause-0 body Call lowers via the per-clause cont-fn path")
assert(classify(5) == 99, "wildcard clause returns 99")
```
