# Source Syntax Front Doors

`src/parser` is now lexer-only. It owns `lexer.rs`, `Tok`, `Token`, token
spans, spacing metadata, and lexer telemetry. The old AST-building
`Parser`/`items.rs`/`expressions.rs`/`patterns.rs` path has been deleted.

Compiler2 parses source in `src/compiler2/frontdoor.rs`. That front door consumes
the shared lexer tokens and produces `QuotedSourceRoot` values directly, rather
than first building old `ast::Program` / `ast::Item` trees. Runtime bootstrap
sources in `src/modules/runtime_library/*.fz` also enter compiler2 through this
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
- **Statement/`eoe` separation**: block parsing (`parse_block_until`) calls
  `skip_newlines()` between statements. A `Tok::Newline` that reaches
  `parse_bp`'s Pratt loop matches none of its arms, so the loop returns the
  completed left-hand side and the block loop treats the newline as the
  boundary between two statements, wrapping multiple statements in
  `__block__`.

There is no `starts_expr_continuation` / `peek_after_newlines`-style
lookahead in the parser. Continuation vs. new-statement is a static,
per-token fact resolved once at tokenize time (leading position) or an
ordinary grammar rule (trailing position) — never a runtime guess about
what a future token "looks like".
