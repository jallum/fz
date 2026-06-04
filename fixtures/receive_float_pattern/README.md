---
purpose: "receive with side-tagged float literals — locks SwitchKind::Float three-path parity"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 29
budget.codegen.instructions: 558
budget.specs.count: 26
budget.planner.worklist_pops: 26
budget.planner.walk_calls: 26
budget.planner.type_fn_calls: 26
budget.planner.matcher_specs: 0
budget.planner.vars: 67
budget.planner.blocks: 26
budget.planner.stmts: 21
budget.planner.dispatches: 36
---

# receive_float_pattern

fz-puj.46 (X5) — receive matcher implementing SwitchKind::Float.

Side-tagged float bit-equality against `1.5` / `2.5` literals. The JIT/AOT
matcher compares the mailbox slot's raw `f64::to_bits()` payload under
side-tag `0xE`; no runtime helper is needed since both sides are
bit-comparable. Interp carries floats as typed interpreter values and observes
the same outcomes.
