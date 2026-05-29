---
purpose: "literal-vs-wildcard clause dispatch (`0` and `_`)"
paths: [jit, interp, aot, repl]
---

# classify_two_clause

Literal-vs-wildcard clause dispatch (`0` and `_`). The behavioural claim is
self-checked in-language, so a clean exit on every path is the pass signal:

```fz
assert(classify(0) == :zero, "literal clause 0 matches :zero")
assert(classify(7) == :other, "wildcard clause matches :other")
```
