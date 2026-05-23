---
purpose: "strict Vec pointer-kind parity for i64, f64, u8, and bit vectors across JIT, interp, and AOT"
paths: [jit, interp, aot]
budget.codegen.functions: 5
budget.codegen.instructions: 283
budget.specs.count: 5
budget.typer.worklist_pops: 12
budget.typer.walk_calls: 12
budget.typer.type_fn_calls: 5
budget.typer.matcher_specs: 0
budget.typer.vars: 53
budget.typer.blocks: 12
budget.typer.stmts: 33
budget.typer.dispatches: 4
---

# vec_three_path_parity

Acceptance fixture for `fz-3ld.11`: all four monotyped Vec layouts
round-trip through JIT, interpreter, and AOT after moving to strict
pointer-kind tags.
