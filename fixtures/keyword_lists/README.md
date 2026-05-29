---
purpose: "Elixir-style keyword lists lower to ordinary lists of atom/value tuples"
paths: [jit, interp, aot, repl]
---

# keyword_lists

Elixir-style keyword lists lower to ordinary lists of `{atom, value}` tuples,
including trailing keyword args and a trailing `do`-block. Self-checked
in-language:

```fz
assert([a: 1, b: 2] == [{:a, 1}, {:b, 2}], "keyword list lowers to a list of atom/value tuples")
assert(echo(label: :work) do 42 end == [{:label, :work}, {:do, 42}], "...")
```
