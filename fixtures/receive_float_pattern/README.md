---
purpose: "receive with boxed float literals — locks SwitchKind::Float three-path parity"
paths: [jit, interp, aot]
budget.codegen.functions: 29
budget.codegen.instructions: 520
budget.specs.count: 17
budget.typer.worklist_pops: 42
budget.typer.walk_calls: 42
budget.typer.type_fn_calls: 17
budget.typer.matcher_specs: 0
budget.typer.vars: 68
budget.typer.blocks: 20
budget.typer.stmts: 27
budget.typer.dispatches: 7
---

# receive_float_pattern

fz-puj.46 (X5) — receive matcher implementing SwitchKind::Float.

Boxed-float bit-equality against `1.5` / `2.5` literals. The matcher
inlines a HeapKind::Float kind check + i64 payload compare; no runtime
helper is needed since both sides are bit-comparable. Interp mirrors
via `Heap::read_float(p).to_bits()`.
