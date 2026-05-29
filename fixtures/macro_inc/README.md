---
purpose: "defmacro + quote/unquote round-trip — two macros, one nested in the other"
paths: [jit, interp, aot, repl]
---

# macro_inc

`defmacro` + `quote`/`unquote` round-trip — two macros, one nested in the other.
Top-level macros (no module), so the claim is behavioural and self-checked
in-language:

```fz
assert(inc(41) == 42, "inc macro expands to +1")
assert(inc(double(20)) == 41, "nested macro expansion")
```
