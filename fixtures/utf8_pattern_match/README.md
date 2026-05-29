---
purpose: "fz-axu.17 (P2) — pattern matching on utf8 string literals"
paths: [jit, interp, aot, repl]
---

# utf8_pattern_match

fz-axu.17 (P2) — pattern matching on utf8 string literals; clause dispatch on
string literals self-checked in-language:

```fz
assert(greet("hi") == :hello, "utf8 literal clause matches")
assert(greet("other") == :unknown, "wildcard clause for non-matching strings")
```
