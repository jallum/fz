---
purpose: A do/end block on a no-parens call becomes a trailing do: keyword arg.
paths: [jit, interp, aot, repl]
oracle: oracle.exs
---

A `do … end` block trailing a no-parens call collapses into the call's final
keyword-list argument, the same shape a paren call produces. `run 1 do 2 end`
calls `run/2` with `1` and `[do: 2]`; `only_block do 42 end` has no positional
arguments and calls `only_block/1` with `[do: 42]`. Destructuring `opts` proves
the `:do` keyword and its value reach the callee end to end.
