---
purpose: "Elixir-style keyword lists lower to ordinary lists of atom/value tuples"
paths: [jit, interp, aot, repl]
---

# keyword_lists

Elixir-style keyword entries are syntax for a list of two-tuples whose first
element is an atom. Calls collect trailing keyword entries into one final list
argument, and a trailing `do ... end` block appends a `do:` entry to that list.
