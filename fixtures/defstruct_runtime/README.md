---
purpose: "source defstruct construction and field access works for named structs"
paths: [jit, interp, aot, repl]
---

# defstruct runtime

Pins `%Module{}` construction from a source `defstruct` declaration and atom-key
field access through dot syntax. The struct is intentionally not `Range`, so the
AOT path must register named schemas generically.
