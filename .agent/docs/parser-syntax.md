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
