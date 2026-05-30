# Parser Syntax Model

Use this when changing surface syntax in `src/parser`.

## Function Items

`fn` declares a public function when it appears inside a module. Public module
functions enter the module interface and must carry public specs when strict
interface validation is enabled.

`fnp` declares a private function. It parses to the same function body shape as
`fn`, can be called by sibling functions in the same module, and is omitted
from public module interfaces. Do not mix `fn` and `fnp` clauses for the same
name/arity.

## Keyword Lists

`Tok::KwKey(name)` is the lexer token for `name:`. The parser treats it as
syntax only in positions that can consume keyword entries:

- list literals: `[a: 1, b: 2]`
- call arguments: `f(x, a: 1, b: 2)`
- call-postfix block sugar: `f(x) do ... end`
- list patterns: `[do: body]`

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

The type surface follows the same rule. The runtime prelude defines ordinary
aliases:

```text
@type keyword() :: [{atom, any}]
@type keyword(t) :: [{atom, t}]
```

## No-Parens Calls

A call may omit its parentheses: `double 21`, `Enum.map xs, f`. The parser
recognizes one when a **callable head** (a bare name or a module-qualified
path, i.e. `Expr::Var` or the `Expr::Index` that `Mod.fun` lowers to) is
followed by a token that **starts an argument** — separated from the head by
spacing, and a value token rather than an operator, container close, or block
keyword. `(` and `[` are excluded: the postfix loop owns them as paren-call and
index. `+`/`-` count only when unary-positioned (space before the operator,
none before its operand), so `foo -1` is the argument `-1` while `foo - 1` is
subtraction.

Arguments are full expressions, so a nested no-parens call owns its own commas:
`f g a, b` is `f(g(a, b))`. Comma greediness depends on position:

- At statement/operand position, arguments are comma-separated greedily.
- Inside a comma-delimited container (list, tuple, map, bitstring, paren call
  args), a no-parens call takes a single argument and leaves the comma to the
  container: `[foo a, b]` is `[foo(a), b]`. This is the `comma_bound` flag;
  blocks, lambda bodies, and parenthesized groupings reset it.

Keyword entries follow the same collapse rule as paren'd calls. Trailing
`key: value` pairs become one final keyword-list argument, and a keyword key in
head position makes the whole argument list a lone keyword list:

```text
foo a, b: 1, c: 2   =>  foo(a, [b: 1, c: 2])
foo b: 1            =>  foo([b: 1])
```

When a no-parens call is itself a keyword value and another keyword entry
follows it, the parse is ambiguous — `b: bar x, c: 2` could fold `c: 2` into
`bar` or leave it in the outer list. fz keeps the trailing keyword in the outer
list (`bar(x)` plus `c: 2`); Elixir folds it into the inner call. The parser
emits a `parse/ambiguous-no-parens-keyword` warning diagnostic to telemetry
(under `[fz, diag, warning]`) so the divergence is observable and the source
can be disambiguated with explicit parentheses.

## Anonymous Functions

`fn` introduces an anonymous function as a non-empty list of clauses, mirroring
Elixir, and is terminated by `end`:

```text
fn x -> x + 1 end
fn (a, b) -> a + b end
fn 0 -> :zero
   n -> n end
fn x when x > 0 -> x
   _ -> 0 end
```

The `end` is required — without a terminator a multi-clause body has no
boundary. Clause structure matches `case` (a pattern list, an optional `when`
guard, `->`, then a body), so the two parsers stay in lockstep. The AST is
`Expr::Lambda(Vec<LambdaClause>)`, each `LambdaClause` carrying `params`, an
optional `guard`, a `body`, and its span.

Only the *direct* clause — a single clause with no guard — lowers and evaluates
today; `lambda_direct_clause` is the one predicate both the interpreter and IR
lowering consult, so the two paths agree on what is runnable. Multi-clause and
guarded lambdas parse but defer execution to the desugar in fz-g58.15 (Arc 3),
where they become pattern-matrix lambdas.

## Boundaries

Special forms such as `if`, `with`, and `quote` still own their dedicated
`do:` parsing paths. Ordinary call keyword parsing should not reinterpret those
forms before their special parsers see them.

Keyword entries are trailing. Once a call or list literal starts parsing
keyword entries, another positional expression is a syntax error.

## Proof Gates

Gate changes here with:

- `cargo test parser::tests::do_block_sugar_tests`
- `cargo test parser::tests::no_parens_call_tests`
- `cargo test parser::tests::no_parens_keyword_ambiguity_tests`
- `cargo test parser::tests::lambda_tests`
- `cargo test private_fns_are_not_interface_exports`
- `cargo test --test fixture_matrix keyword_lists`
- `cargo test --test fixture_matrix no_parens_keyword`
- `cargo test test_runner::tests`
