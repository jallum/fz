---
purpose: "two workers both block on receive simultaneously; exercises scheduler managing multiple Blocked processes"
paths: [jit, interp, aot, repl]
---

# multi_relay

Two workers both block on `receive` simultaneously; exercises the scheduler
managing multiple Blocked processes. The deterministic single-threaded schedule
relays the two results in order, self-checked in-language:

```fz
a = receive do x -> x end
b = receive do x -> x end
assert(a == 20, "first worker doubled 10")
assert(b == 22, "second worker doubled 11")
```
