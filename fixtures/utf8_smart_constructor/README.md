---
purpose: "fz-axu.19 (P4) — Utf8 smart constructors over raw bytes"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 8
budget.codegen.instructions: 157
budget.specs.count: 8
budget.planner.worklist_pops: 16
budget.planner.walk_calls: 16
budget.planner.type_fn_calls: 8
budget.planner.matcher_specs: 0
budget.planner.vars: 41
budget.planner.blocks: 10
budget.planner.stmts: 19
budget.planner.dispatches: 10
---

# utf8_smart_constructor

Exercises the S2 surface: `Utf8.from_bytes/1` returns `{:ok, utf8}`
for valid UTF-8 and `{:error, :invalid_utf8}` for raw bytes that
don't decode. `Utf8.valid?/1` is the same check without the wrap.
