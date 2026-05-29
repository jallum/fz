---
purpose: "fz-siu.12 — spawn/2 with min_heap_size hint behaves identically to spawn/1"
paths: [jit, interp, aot, repl]
---

# spawn2_basic

fz-siu.12 — `spawn/2` with a `min_heap_size` hint behaves identically to
`spawn/1`. The relayed tag is self-checked in-language:

```fz
spawn(fn () -> child(42), 4096)
got = receive do x -> x end
assert(got == 42, "spawn/2 with min_heap_size hint behaves like spawn/1")
```
