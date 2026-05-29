---
purpose: "spawn + send + receive — parent blocks on receive, prints the message"
paths: [jit, interp, aot, repl]
---

# concurrency_ping_pong

spawn + send + receive — the parent blocks on `receive` until the child sends,
self-checked in-language:

```fz
spawn(child)
got = receive do x -> x end
assert(got == 42, "parent blocks on receive until the child sends")
```
