---
purpose: "fz-ul4.29.5 — spawn-with-captures lift (was forbidden v1)"
paths: [jit, interp, aot, repl]
---

# spawn_with_captures

fz-ul4.29.5 — spawn-with-captures lift (was forbidden in v1). The spawned
closure captures `tag` from the enclosing scope and sends it back; the relayed
value is self-checked in-language:

```fz
spawn(fn () -> send(1, tag))
receive()
```

```fz
assert(parent(99) == 99, "spawned closure captures tag and relays it back")
```

Pre-.29.5, `fz_spawn` asserted `captured.len() == 0`. With the stub design the
capture set is lifted into the spawned process's frame instead.
