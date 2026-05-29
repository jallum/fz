---
purpose: "assert/2 + refute/2 carry a caller-supplied message; the truthy path returns nil cleanly across all four paths"
paths: [jit, interp, aot, repl]
---

# assert_message

Pins the two-argument forms of the `Kernel` assertion prelude:

```fz
assert(1 + 1 == 2, "arithmetic still works")
refute(1 == 2, "one is not two")
```

`assert/2` and `refute/2` delegate to the existing `panic/1` extern on the
failing branch, so the only new behaviour over `assert/1`/`refute/1` is which
string reaches the abort. This fixture exercises the *passing* branch — no
`dbg`, no `expected.txt`, so a clean exit on every path is the pass signal,
following the [[make_ref_distinct]] template.

The *failing* branch cannot be a passing fixture (a runtime abort is a nonzero
exit, which the matrix scores as a failure before any output comparison). The
message-reaches-abort behaviour is pinned instead by
`tests/assert_message_parity.rs`, which runs `assert(false, "...")` through
interp / JIT / AOT / REPL and asserts the rendered `fz panic: <message>`.
