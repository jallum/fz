---
purpose: "fz-axu.19 (P4) — Utf8 smart constructors over raw bytes"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 7
budget.codegen.instructions: 90
budget.specs.count: 7
budget.planner.worklist_pops: 17
budget.planner.walk_calls: 17
budget.planner.type_fn_calls: 7
budget.planner.matcher_specs: 0
budget.planner.vars: 60
budget.planner.blocks: 13
budget.planner.stmts: 29
budget.planner.dispatches: 7
---

# utf8_smart_constructor

Exercises the S2 surface: `Utf8.from_bytes/1` returns `{:ok, utf8}`
for valid UTF-8 and `{:error, :invalid_utf8}` for raw bytes that
don't decode. `Utf8.valid?/1` is the same check without the wrap.
