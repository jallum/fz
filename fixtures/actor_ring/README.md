---
purpose: "N-hop actor ring with self()-capture + spawn-with-captures + multi-clause CPS-split-in-body; closes fz-g8v by exercising the fz-qbg.2 multi-clause body cont-fn path end-to-end"
paths: [jit, interp, aot, repl]
---

# actor_ring

N-hop actor ring with `self()`-capture + spawn-with-captures + multi-clause
CPS-split-in-body; closes fz-g8v by exercising the fz-qbg.2 multi-clause body
cont-fn path end-to-end. The accumulated hop count is self-checked in-language:

```fz
send(head, 0)
got = receive()
assert(got == 5, "5-hop actor ring increments 0 once per hop")
```
