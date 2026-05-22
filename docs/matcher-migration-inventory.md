# Matcher Migration Inventory

Status: completed by `fz-puj.55`.

`fz-puj.54` moved executable matching to an AST-free `Matcher`.
`fz-puj.55` removed the remaining bridge scaffolding and stale leaf
precondition shape.

## Current Boundary

AST patterns and AST expressions remain valid in the frontend, parser,
pattern checker, macro system, and source-to-PatternMatrix construction. They are not
stored in runtime-facing matcher execution.

The executable matcher path is:

```text
Pattern -> PatternMatrix rows -> Matcher graph -> inline lowering or receive ABI lowering
```

## Remaining Intentional AST Use

- `Row.patterns` and `Row.guard` are PatternMatrix compiler input.
- `pattern_check` builds PatternMatrices from AST to report unreachable and
  inexhaustive matches.
- `ir_lower` builds PatternMatrices from source clauses before compiling Matchers.

Those are frontend/lowering inputs, not executable matcher fallback paths.

## Removed Debt

- Receive no longer carries AST clauses for matching execution.
- Receive probing reuses the lowered Matcher.
- General dispatch no longer lowers through a separate bridge tree.
- Matcher leaves no longer carry preconditions; preconditions are explicit
  `MatcherTest::Type` nodes.
