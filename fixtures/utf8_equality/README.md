---
purpose: "fz-axu.18 (P3) — `==` between utf8 strings compares bytes"
paths: [jit, interp, aot]
budget.codegen.functions: 2
budget.codegen.instructions: 65
budget.specs.count: 2
budget.typer.worklist_pops: 3
budget.typer.walk_calls: 3
budget.typer.type_fn_calls: 2
budget.typer.matcher_specs: 0
budget.typer.vars: 30
budget.typer.blocks: 5
budget.typer.stmts: 15
budget.typer.dispatches: 1
---

# utf8_equality

Verifies that `==` over utf8 strings does bytewise equality. The brand
is type-system metadata; the runtime compares underlying bitstrings.
