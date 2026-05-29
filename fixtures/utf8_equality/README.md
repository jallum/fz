---
purpose: "fz-axu.18 (P3) — `==` between utf8 strings compares bytes"
paths: [jit, interp, aot, repl]
---

# utf8_equality

fz-axu.18 (P3) — `==` between utf8 strings compares bytes, self-checked
in-language:

```fz
assert("hi" == "hi", "equal utf8 strings compare equal")
refute("hi" == "bye", "different utf8 strings compare unequal")
assert("héllo" == "héllo", "multibyte utf8 strings compare by bytes")
```
