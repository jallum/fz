---
purpose: "fz-axu.19 (P4) — Utf8 smart constructors over raw bytes"
paths: [jit, interp]
---

# utf8_smart_constructor

Exercises the S2 surface: `Utf8.from_bytes/1` returns `{:ok, utf8}`
for valid UTF-8 and `{:error, :invalid_utf8}` for raw bytes that
don't decode. `Utf8.valid?/1` is the same check without the wrap.
