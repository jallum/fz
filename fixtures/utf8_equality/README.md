---
purpose: "fz-axu.18 (P3) — `==` between utf8 strings compares bytes"
paths: [jit, interp, aot]
---

# utf8_equality

Verifies that `==` over utf8 strings does bytewise equality. The brand
is type-system metadata; the runtime compares underlying bitstrings.
