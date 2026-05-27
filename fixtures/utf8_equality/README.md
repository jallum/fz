---
purpose: "fz-axu.18 (P3) — `==` between utf8 strings compares bytes"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 48
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 16
budget.planner.blocks: 1
budget.planner.stmts: 12
budget.planner.dispatches: 0
---

# utf8_equality

Verifies that `==` over utf8 strings does bytewise equality. The brand
is type-system metadata; the runtime compares underlying bitstrings.
