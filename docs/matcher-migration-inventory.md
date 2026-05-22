# Matcher Migration Inventory

`fz-puj.54` moves executable matching to one AST-free `Matcher`.
This inventory freezes the source seams that still carry AST into
matching execution before that migration starts.

## Executable AST Carriers

- `src/pattern_matrix.rs`
  - `Row.patterns: Vec<Spanned<Pattern>>`
  - `Row.guard: Option<Spanned<Expr>>`
  - `Decision::Leaf.guard: Option<Spanned<Expr>>`
  - `Decision::PerRow.row: Row`
  - `find_unspecializable_row` sends `Map`, `Bitstring`, and `Pinned`
    through `PerRow`.
- `src/fz_ir.rs`
  - `Term::ReceiveMatched.decision: Arc<pattern_matrix::Decision>`
  - `Term::ReceiveMatched.clauses: Vec<ReceiveClause>`
  - `ReceiveClause.pattern: Spanned<Pattern>`
- `src/ir_lower.rs`
  - `lower_decision_per_row` lowers a `Decision::PerRow` by walking the
    row's AST pattern.
  - `build_receive_matrix` rebuilds receive rows from AST clauses.
  - `lower_receive` stores both AST receive clauses and a cached
    `Decision`.
  - `inline_pure_user_fn_calls_in_guard` and `substitute_vars_in_expr`
    implement guard helper calls by AST substitution.
- `src/ir_interp.rs`
  - `execute_decision` delegates `Decision::PerRow` to
    `try_match_pattern`.
  - `try_match_pattern` is an AST pattern walker for receive probes.
  - Guard failure after a receive match currently misses the receive
    rather than following `Decision::Leaf.on_guard_fail`.
- `src/ir_codegen_receive.rs`
  - `emit_matcher_body_from_decision` rebuilds `Matrix`/`Decision` from
    `ReceiveClause.pattern` instead of consuming the cached decision.
  - `emit_decision` delegates `Decision::PerRow` to `compile_pattern`.
  - `compile_pattern` is an AST pattern walker for pinned, map, list
    fallback, and unsupported bitstring.

## Current Characterization

- Shared constructor routing and first-match ordering are covered in
  `pattern_matrix` tests.
- Guard fallthrough shape is covered by `guarded_row_rejects_to_next_reachable_row`
  and receive oracle tests in `ir_lower`.
- Receive interpreter probes reuse the lowered decision, covered by
  `receive_reuses_lowered_decision_during_interp_probes`.
- `Map`, `Bitstring`, and `Pinned` currently enter `Decision::PerRow`;
  this is intentional debt, not the target architecture.
- Receive native codegen supports pinned/map/list fallback through the
  AST walker, but bitstring currently misses until `fz-puj.54.7` /
  `fz-puj.50`.

## Migration Target

After `fz-puj.54`, executable matcher paths should contain no
`Spanned<Pattern>` or `Spanned<Expr>` payloads. AST remains valid in the
frontend, parser, pattern checker, macro system, and migration tests, but
not inside the runtime-facing matcher representation.
