---
purpose: "fz-axu.19 (P4) — Utf8 smart constructors over raw bytes"
paths: [jit, interp, aot, repl, fz2-run, fz2-interp, fz2-build]
budget.codegen.functions: 10
budget.codegen.instructions: 201
budget.specs.count: 10
budget.planner.worklist_pops: 10
budget.planner.walk_calls: 10
budget.planner.type_fn_calls: 10
budget.planner.matcher_specs: 0
budget.planner.vars: 38
budget.planner.blocks: 12
budget.planner.stmts: 19
budget.planner.dispatches: 12
---

# utf8_smart_constructor

Exercises the S2 surface: `Utf8.from_bytes/1` returns `{:ok, utf8}`
for valid UTF-8 and `{:error, :invalid_utf8}` for raw bytes that
don't decode. `Utf8.valid?/1` is the same check without the wrap.
