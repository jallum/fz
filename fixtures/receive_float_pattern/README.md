---
purpose: "receive with boxed float literals — locks SwitchKind::Float three-path parity"
paths: [jit, interp, aot]
budget.codegen.functions: 27
budget.codegen.instructions: 696
budget.specs.count: 11
budget.typer.worklist_pops: 24
budget.typer.walk_calls: 24
budget.typer.type_fn_calls: 11
budget.typer.matcher_specs: 0
budget.typer.vars: 59
budget.typer.blocks: 14
budget.typer.stmts: 27
budget.typer.dispatches: 1
---

# receive_float_pattern

fz-puj.46 (X5) — receive matcher implementing SwitchKind::Float.

Boxed-float bit-equality against `1.5` / `2.5` literals. The matcher
inlines a HeapKind::Float kind check + i64 payload compare; no runtime
helper is needed since both sides are bit-comparable. Interp mirrors
via `Heap::read_float(p).to_bits()`.
