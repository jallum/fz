---
purpose: "mutual recursion — is_even/is_odd call each other; exercises cross-function recursive dispatch"
paths: [jit, interp, aot, repl]
---

# mutual_recursion

`is_even`/`is_odd` call each other; exercises cross-function recursive dispatch.
The behavioural claim is self-checked in-language:

```fz
assert(is_even(10), "10 is even")
assert(is_odd(7), "7 is odd")
```
