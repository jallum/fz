---
purpose: "receive with boxed float literals — locks SwitchKind::Float three-path parity"
paths: [jit, interp, aot]
budget.codegen.min_functions: 27
budget.codegen.max_functions: 27
budget.codegen.min_instructions: 556
budget.codegen.max_instructions: 836
budget.specs.min_count: 29
budget.specs.max_count: 44
---

# receive_float_pattern

fz-puj.46 (X5) — receive matcher implementing SwitchKind::Float.

Boxed-float bit-equality against `1.5` / `2.5` literals. The matcher
inlines a HeapKind::Float kind check + i64 payload compare; no runtime
helper is needed since both sides are bit-comparable. Interp mirrors
via `Heap::read_float(p).to_bits()`.
