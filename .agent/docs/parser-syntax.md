# Parser Syntax Model

Use this when changing surface syntax in `src/parser`.

## Keyword Lists

`Tok::KwKey(name)` is the lexer token for `name:`. The parser treats it as
syntax only in positions that can consume keyword entries:

- list literals: `[a: 1, b: 2]`
- call arguments: `f(x, a: 1, b: 2)`
- call-postfix block sugar: `f(x) do ... end`

The AST representation is deliberately ordinary data:

```text
[a: 1, b: 2]
=> Expr::List([
     Expr::Tuple([Expr::Atom("a"), Expr::Int(1)]),
     Expr::Tuple([Expr::Atom("b"), Expr::Int(2)])
   ])
```

Calls collect trailing keyword entries into one final list argument. A trailing
`do ... end` block appends a `do:` pair to that same final list, so
`f(x, timeout: 10) do 42 end` has the call shape:

```text
f(x, [timeout: 10, do: 42])
```

This matches Elixir's user-facing model without adding a keyword-list AST node
or runtime type.

## Boundaries

Special forms such as `if`, `with`, and `quote` still own their dedicated
`do:` parsing paths. Ordinary call keyword parsing should not reinterpret those
forms before their special parsers see them.

Keyword entries are trailing. Once a call or list literal starts parsing
keyword entries, another positional expression is a syntax error.

## Proof Gates

Gate changes here with:

- `cargo test parser::tests::do_block_sugar_tests`
- `cargo test --test fixture_matrix keyword_lists`
- `cargo test test_runner::tests`
