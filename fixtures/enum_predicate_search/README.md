---
purpose: "Enum predicate and search functions match Elixir and halt as soon as the answer is known"
paths: [jit, interp, aot, repl]
timeout.interp_secs: 15
timeout.repl_secs: 15
oracle: oracle.exs
---

Exercises the `fz-g58.25` Enum predicate/search layer:
`all?/1,2`, `any?/1,2`, `empty?/1`, `find/2,3`, `find_index/2`, and
`find_value/2,3`.

The final cases would panic if the runtime kept reducing after a decisive
answer, so this fixture also pins the `reduce_while/3` early-exit contract.
