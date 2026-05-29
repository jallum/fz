---
purpose: "two-hop process relay — main → first_relay → second_relay → main; exercises multi-process message chaining"
paths: [jit, interp, aot, repl]
---

# three_process_chain

Two-hop process relay — `main → first_relay → second_relay → main`, +1 at each
hop; exercises multi-process message chaining. The final value is self-checked
in-language:

```fz
got = receive do x -> x end
assert(got == 42, "main -> first_relay -> second_relay -> main, +1 each hop")
```
