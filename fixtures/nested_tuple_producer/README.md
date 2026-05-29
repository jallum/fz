---
purpose: "nested tuple producer call inside an outer tuple literal; keeps tuple DP live across continuations"
paths: [jit, interp, aot, repl]
---

# nested_tuple_producer

A nested tuple-producer call inside an outer tuple literal; the inner `pair/1`
suspends on a `receive`, so the outer tuple's destination must stay live across
the continuation. Self-checked in-language:

```fz
result = {1, pair(2)}
assert(result == {1, {2, 2}}, "nested tuple producer keeps tuple DP live across the receive continuation")
```
