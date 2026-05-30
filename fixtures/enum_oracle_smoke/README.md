---
purpose: "Enum.sort/1 matches Elixir; expected.txt is owned by the oracle.exs twin"
paths: [jit, interp, aot, repl]
oracle: oracle.exs
---

# enum_oracle_smoke

Demonstrates the Elixir oracle. `oracle.exs` is the Elixir twin of `input.fz`.
Running it under `elixir` produces `expected.txt`; the four fz paths must
reproduce the same `expected.txt`. fz `dbg` and Elixir `IO.inspect` render
values identically, so the goldens are the same text.

`Enum.sort/1` already matches Elixir's API. The `oracle_goldens_match_elixir`
static test owns `expected.txt`; per-path `BLESS` does not rewrite it.
