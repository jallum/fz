# Source Syntax Front Doors

`src/parser` is now lexer-only. It owns `lexer.rs`, `Tok`, `Token`, token
spans, spacing metadata, and lexer telemetry. The old AST-building
`Parser`/`items.rs`/`expressions.rs`/`patterns.rs` path has been deleted.

Compiler2 parses source in `src/compiler2/frontdoor.rs`. That front door consumes
the shared lexer tokens and produces `QuotedSourceRoot` values directly, rather
than first building old `ast::Program` / `ast::Item` trees. Runtime bootstrap
sources in `lib/*.fz` also enter compiler2 through this
quoted-source path.

Keep this boundary crisp:

- Add token-shape changes in `src/parser/lexer.rs` and `lexer_test.rs`.
- Add source grammar changes in `src/compiler2/frontdoor.rs` and
  `frontdoor_test.rs`.
- Do not revive `Parser::new`, `parse_program`, `parse_prelude`, or
  `parse_expr_eof`; old callers should move to compiler2 quoted source.

## Newline continuation is grammar-owned, not a parser lookahead

Physical newlines are first-class `Tok::Newline` tokens. Whether a newline
ends a statement or continues the previous expression falls out of which
token is on either side of it — the frontdoor parser never peeks past a
newline to guess intent.

- **Trailing eol** (operator/`.` at the END of a line): each infix
  production in `FrontDoorParser::parse_bp` calls `skip_newlines()` right
  after consuming its operator, before parsing the right-hand side. Every
  `Tok::Dot`-consuming production does the same right after consuming the
  dot: `finish_remote_target` and `finish_closure_call` (value/call access),
  `parse_alias_expr` (alias-path chains, e.g. `Foo.\n  Bar`), the
  capture-target dot chain in `parse_capture_target` (e.g. `&Foo.\n  bar/1`),
  and `parse_upper_path` (the shared path parser behind
  `alias`/`import`/`require`/`defmodule`/protocol module paths). Dot
  consumes trailing eol by construction regardless of what it's chaining —
  this is ordinary trailing-position grammar, unconditional, no
  classification needed. `parse_alias_expr`'s loop guard additionally uses
  `peek_non_newline_from` to look past a newline run before committing to
  consume the dot, since an alias-path dot only continues the chain when an
  uppercase segment follows (unlike remote access, which continues
  unconditionally after any dot).
- **Leading eol** (operator at the START of a line): the lexer decides.
  `parser::lexer::is_infix_only_continuation` classifies each operator/`.`
  token by whether its grammar production can *only* ever be infix/postfix
  (it has no unary/prefix form). `Lexer::tokenize` drops any run of
  `Tok::Newline` immediately preceding such a token, so the parser sees it
  glued to the prior expression exactly as if it had been written on one
  line — no `Tok::Newline` ever reaches `parse_bp` for these. `Tok::Minus`
  and `Tok::Percent` are excluded from that set on purpose: both are dual
  prefix/infix in fz — `parse_prefix` accepts `-` as unary negation and `%`
  as a `%Foo{...}` struct literal, while `infix_bp` gives them subtraction
  and modulo — so a `-` or `%` leading a fresh physical line always starts a
  *new* statement (mirrors Elixir's tokenizer, where a prefix-capable
  operator never swallows a preceding eol; `%` has no modulo in Elixir, so
  that dual role is fz-specific).
- **Statement/`eoe` separation**: a `Tok::Newline` that reaches `parse_bp`'s
  Pratt loop matches none of its arms, so the loop returns the completed
  left-hand side. Every newline-delimited sequence then calls
  `require_newline_or_terminator`: another expression, item, or clause is legal
  only after a physical newline; an enclosing `end`/`else`/`after` may follow
  immediately. Spaces alone are never a statement separator, so `a = 1 2` is
  rejected at the `2` instead of becoming a block whose extra expression can
  be discarded downstream. Inline grammar such as call arguments, lambdas,
  and trailing `do` blocks remains inside `parse_bp` and its sub-productions
  before the sequence boundary is checked. A block with multiple separated
  statements is wrapped in `__block__`. The keyword-list parser preserves this
  ownership: it consumes newlines only when the next non-newline token is its
  comma or closing delimiter. A newline after a no-parens keyword call is left
  for the enclosing block, so the next call remains a separate statement.

There is no `starts_expr_continuation` / `peek_after_newlines`-style
lookahead in the parser. Continuation vs. new-statement is a static,
per-token fact resolved once at tokenize time (leading position) or an
ordinary grammar rule (trailing position) — never a runtime guess about
what a future token "looks like".

## `when` and trailing `do` belong to expression grammar

`when` is a reserved operator token, but it is not definition grammar. The
front door's Pratt table is its one binary parse authority: it is
right-associative, weaker than `=` and `::`, and stronger than the comma and
clause boundaries owned by enclosing productions. A guarded definition, case
pattern, `with` pattern, or single-argument anonymous clause therefore receives
the same `{:when, meta, [left, guard]}` expression shape. The anonymous-function
reader only packages the distinct multi-argument clause shape
`{:when, meta, [arg1, ..., guard]}` after the expression parser has parsed the
guard; it does not own `when` precedence. The `when` following an `extern`
return type remains a different production: it introduces type-variable
constraints, not a guard expression.

A trailing `do ... end` block belongs to the outermost unparenthesized call.
While the parser reads that call's no-parens arguments, nested unmatched calls
may not consume the block; after the arguments are complete, the outer call
appends one fresh `[do: body]` argument. `, do:` remains ordinary keyword-call
syntax: `outer value: 1, do: 42` has one `[value: 1, do: 42]` argument, while
`def head, do: body` has the already-parsed head followed by that keyword-list
argument.

Every matched delimiter reopens local block ownership for its contents and
restores the enclosing suppression when it closes. Thus
`outer(inner() do body end)` and `outer (inner() do body end)` give the block
to `inner`, as do nested calls inside call arguments and container literals;
`outer inner() do body end` gives it to `outer`.

Whitespace also keeps Elixir's call/grouping distinction: `callee(arg)` is a
parenthesized call, while `callee (arg)` is a no-parens call whose first
argument is the grouped expression `(arg)`. This lets an ordinary identifier
macro receive operator heads such as
`def (left :: integer) + (right :: integer), do: left + right` without a
definition-only operand parser.

## Heredocs are string literals

`"""` opens a heredoc, which lexes to a single `Tok::Binary` holding its lines
with the closing delimiter's indentation stripped. It is a string LITERAL, not
a raw string, so it carries both of a literal's behaviours:

- **Escapes are processed.** Source `one\"two` stores `one"two`. A lone `"`
  needs no escape, since only `"""` terminates the heredoc, so a backslash that
  should survive into the text has to be doubled: `"{\\"a\\": 1}"` in the source
  stores `"{\"a\": 1}"`.
- **Interpolation runs.** `"a#{1 + 1}b"` inside a heredoc stores `a2b`.
  `\#{x}` suppresses it and stores `#{x}`; `dbg` re-escapes a literal `#{` when
  it renders, so a round trip looks doubled and is not.

Both apply to `@doc """ ... """` and `@moduledoc """ ... """`, which take the
same string token. Documentation that quotes fz syntax is therefore executable
text: a doc explaining interpolation contains `#{...}` and will interpolate it,
and an unbound name there currently changes what the module compiles to without
reporting anything (fz-5xp.96). Escape the sigil in prose that describes it.
