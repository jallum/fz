---
purpose: "Enum tier-0 functions return Elixir-style public values across List, Range, and Map"
paths: [jit, interp, aot, repl]
oracle: oracle.exs
timeout.interp_secs: 15
timeout.repl_secs: 15
---

Exercises the reduce-based public `Enum` surface that later Enum functions build
on: `reduce/2`, `reduce/3`, `reduce_while/3`, `each/2`, `count/1`, `count/2`,
`member?/2`, `to_list/1`, and `reverse/1,2`.

The interp/repl timeout overrides are temporary correctness-only coverage for
the protocol-first tier-0 surface. `fz-g58.52` owns restoring the default 3s
fixture gate by removing these two overrides.
