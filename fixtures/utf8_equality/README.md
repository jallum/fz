---
purpose: "fz-axu.18 (P3) — `==` between utf8 strings compares bytes"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 2
budget.codegen.instructions: 58
budget.specs.count: 2
budget.planner.worklist_pops: 3
budget.planner.walk_calls: 3
budget.planner.type_fn_calls: 2
budget.planner.matcher_specs: 0
budget.planner.vars: 30
budget.planner.blocks: 5
budget.planner.stmts: 15
budget.planner.dispatches: 1
---

# utf8_equality

Verifies that `==` over utf8 strings does bytewise equality. The brand
is type-system metadata; the runtime compares underlying bitstrings.
