---
purpose: "fz-axu.16 (P1) — utf8 string literal prints as `\"text\"`"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 11
budget.specs.count: 1
budget.typer.worklist_pops: 1
budget.typer.walk_calls: 1
budget.typer.type_fn_calls: 1
budget.typer.matcher_specs: 0
budget.typer.vars: 6
budget.typer.blocks: 2
budget.typer.stmts: 3
budget.typer.dispatches: 0
---

# utf8_literal_print

End-to-end smoke for the L3 → typer → R2 print path: a literal `"hi"`
lowers to a utf8-branded const bitstring; print's payload-aware
rendering surfaces it as a quoted string in stdout.

## Notes

AOT path elided pending the AOT shim wiring for `fz_print_value` over
branded bitstrings — same as the other print-bearing fixtures in this
suite (see fz-xx8 follow-up).
