---
purpose: "trailing/leading keyword lists in no-parens calls parse into one list arg; output matches Elixir"
paths: [jit, interp, aot, repl]
oracle: oracle.exs
---

# no_parens_keyword

Exercises Elixir-style keyword-list arguments to no-parens calls. `run 1, b: 2,
c: 3` parses as `run(1, [b: 2, c: 3])` — the trailing `key: value` pairs collapse
into a single keyword-list argument — and `only_opts x: 9` parses as
`only_opts([x: 9])`, a lone leading keyword list. Each body destructures the
list to show the runtime shape (a list of `{key, value}` tuples). `oracle.exs`
is the Elixir twin; both print the same atoms and integers, so `expected.txt`
is owned by the oracle.
