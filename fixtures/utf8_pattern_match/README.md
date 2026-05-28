---
purpose: "fz-axu.17 (P2) — pattern matching on utf8 string literals"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 7
budget.codegen.instructions: 222
budget.specs.count: 7
budget.planner.worklist_pops: 12
budget.planner.walk_calls: 12
budget.planner.type_fn_calls: 7
budget.planner.matcher_specs: 0
budget.planner.vars: 100
budget.planner.blocks: 35
budget.planner.stmts: 71
budget.planner.dispatches: 12
---

# utf8_pattern_match

Verifies that a `case` expression matching against string-literal
patterns dispatches correctly. Both patterns and subjects lower to
utf8-branded const bitstrings; the per-row eq check compares the
underlying bytes.
