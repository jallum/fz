---
purpose: "fz-axu.17 (P2) — pattern matching on utf8 string literals"
paths: [jit, interp, aot]
budget.codegen.functions: 9
budget.codegen.instructions: 486
budget.specs.count: 9
budget.typer.worklist_pops: 22
budget.typer.walk_calls: 22
budget.typer.type_fn_calls: 9
budget.typer.matcher_specs: 0
budget.typer.vars: 72
budget.typer.blocks: 30
budget.typer.stmts: 42
budget.typer.dispatches: 12
---

# utf8_pattern_match

Verifies that a `case` expression matching against string-literal
patterns dispatches correctly. Both patterns and subjects lower to
utf8-branded const bitstrings; the per-row eq check compares the
underlying bytes.
