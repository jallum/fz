---
purpose: "fz-axu.16 (P1) — utf8 string literal prints as `\"text\"`"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 11
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 6
budget.planner.blocks: 2
budget.planner.stmts: 3
budget.planner.dispatches: 0
---

# utf8_literal_print

End-to-end smoke for the L3 → planner → R2 print path: a literal `"hi"`
lowers to a utf8-branded const bitstring; print's payload-aware
rendering surfaces it as a quoted string in stdout.

## Notes

AOT path elided pending the AOT shim wiring for `fz_print_value` over
branded bitstrings — same as the other print-bearing fixtures in this
suite (see fz-xx8 follow-up).
