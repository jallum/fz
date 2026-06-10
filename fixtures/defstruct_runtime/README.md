---
purpose: "source defstruct construction and field access works for named structs"
paths: [jit, interp, aot, repl, fz2-run, fz2-interp, fz2-build]
---

# defstruct runtime

Pins `%Module{}` construction from a source `defstruct` declaration and atom-key
field access through dot syntax. The struct is intentionally not `Range`, so the
AOT path must register named schemas generically.
