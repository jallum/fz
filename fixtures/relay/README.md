---
purpose: "one-hop relay — spawned child blocks on receive before parent sends; exercises non-blocking spawn + receive-parks semantics"
paths: [jit, interp, aot, repl]
---

# relay

One-hop relay — the spawned child blocks on `receive` before the parent sends,
exercising non-blocking spawn + receive-parks semantics. The relayed value is
self-checked in-language:

```fz
got = receive do x -> x end
assert(got == 42, "spawned child blocks on receive, then relays 41+1")
```
