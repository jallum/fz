---
purpose: "nested tuple producer call inside an outer tuple literal; keeps tuple DP live across continuations"
paths: [jit, interp, aot, repl]
---

# nested_tuple_producer

`main/0` builds an outer tuple whose second field comes from `pair/1`.
`pair/1` sends to and receives from its own mailbox before returning the
inner tuple, so the producer remains behind a real continuation boundary
in all execution paths.
