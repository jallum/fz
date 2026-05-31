---
purpose: "Enum take/drop/split functions match Elixir, including negative counts and predicate stop points"
paths: [jit, interp, aot, repl]
oracle: oracle.exs
timeout.interp_secs: 15
timeout.repl_secs: 15
---

Exercises the `fz-g58.26` Enum take/drop/split layer:
`take/2`, `take_while/2`, `take_every/2`, `drop/2`, `drop_while/2`,
`drop_every/2`, `split/2`, `split_while/2`, and `split_with/2`.

The negative-count cases pin Elixir's two-pass semantics for `take/2`,
`drop/2`, and `split/2`. The final `*_while` cases would panic if the
predicate kept running after the first falsy answer, so the fixture also
proves the protocol path stops exactly where it should.
