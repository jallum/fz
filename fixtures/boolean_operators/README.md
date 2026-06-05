---
purpose: "boolean operators are Elixir's `and` / `or` / `not` (no C-style `&&` / `||` / `!`) — truth table, precedence, and guard use"
paths: [jit, interp, aot, repl]
---
`and` binds tighter than `or`; `not` is the tightest unary prefix. The same
operators are valid in `when` guards. The C-style spellings `&&` / `||` / `!`
are not operators in fz and are rejected at lex time.
