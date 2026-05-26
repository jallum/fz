---
purpose: "receive with side-tagged float literals — locks SwitchKind::Float three-path parity"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 20
budget.codegen.instructions: 534
budget.specs.count: 17
budget.planner.worklist_pops: 42
budget.planner.walk_calls: 42
budget.planner.type_fn_calls: 17
budget.planner.matcher_specs: 0
budget.planner.vars: 68
budget.planner.blocks: 20
budget.planner.stmts: 27
budget.planner.dispatches: 7
---

# receive_float_pattern

fz-puj.46 (X5) — receive matcher implementing SwitchKind::Float.

Side-tagged float bit-equality against `1.5` / `2.5` literals. The JIT/AOT
matcher compares the mailbox slot's raw `f64::to_bits()` payload under
side-tag `0xE`; no runtime helper is needed since both sides are
bit-comparable. Interp carries floats as typed interpreter values and observes
the same outcomes.
