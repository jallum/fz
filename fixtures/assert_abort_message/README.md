---
purpose: "a failed assert aborts with the caller's message on every path (expect-failure medium)"
paths: [jit, interp, aot, repl]
expect: abort
---

# assert_abort_message

A failed `assert(_, msg)` routes the caller's message through `Kernel.panic` and
aborts. The program exits nonzero on every path; the `expected.stderr` golden
pins that the message reaches stderr. This is the canonical example of the
expect-failure medium.
