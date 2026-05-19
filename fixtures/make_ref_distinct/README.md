---
purpose: "fz-ht5 — make_ref() returns a distinct opaque ref on every call"
paths: [jit, interp, aot]
---

# make_ref_distinct

fz-ht5 — Two successive calls to `make_ref()` must return distinct values. The
value's type is the opaque `ref`; arithmetic on it is rejected by the typer
(separate fixture / negative test).
