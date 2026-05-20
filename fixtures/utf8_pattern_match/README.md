---
purpose: "fz-axu.17 (P2) — pattern matching on utf8 string literals"
paths: [jit, interp]
---

# utf8_pattern_match

Verifies that a `case` expression matching against string-literal
patterns dispatches correctly. Both patterns and subjects lower to
utf8-branded const bitstrings; the per-row eq check compares the
underlying bytes.
