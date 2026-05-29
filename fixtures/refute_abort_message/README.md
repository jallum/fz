---
purpose: "a failed refute aborts with the caller's message on every path"
paths: [jit, interp, aot, repl]
expect: abort
---

# refute_abort_message

A failed `refute(_, msg)` — its condition held — routes the caller's message
through `Kernel.panic` and aborts. The program exits nonzero on every path; the
`expected.stderr` golden pins that the message reaches stderr. The `assert` mate
is `assert_abort_message`.
