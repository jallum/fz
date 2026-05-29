---
purpose: "100k-deep self-recursion must TCO — exits cleanly with the accumulated count"
paths: [jit, interp, aot, repl]
---

# tail_recursion

100k-deep self-recursion must tail-call-optimize: if it didn't, the stack would
blow before the assertion runs. A clean exit with `count(100000, 0) == 100000`
on every path is the pass signal.

```fz
assert(count(100000, 0) == 100000, "100k-deep self-recursion accumulates and must TCO")
```
