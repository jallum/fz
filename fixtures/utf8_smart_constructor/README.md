---
purpose: "fz-axu.19 (P4) — Utf8 smart constructors over raw bytes"
paths: [jit, interp, aot]
budget.codegen.functions: 7
budget.codegen.instructions: 259
budget.specs.count: 7
budget.typer.worklist_pops: 17
budget.typer.walk_calls: 17
budget.typer.type_fn_calls: 7
budget.typer.matcher_specs: 0
budget.typer.vars: 60
budget.typer.blocks: 13
budget.typer.stmts: 29
budget.typer.dispatches: 7
---

# utf8_smart_constructor

Exercises the S2 surface: `Utf8.from_bytes/1` returns `{:ok, utf8}`
for valid UTF-8 and `{:error, :invalid_utf8}` for raw bytes that
don't decode. `Utf8.valid?/1` is the same check without the wrap.
