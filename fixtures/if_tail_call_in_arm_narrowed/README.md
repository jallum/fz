---
purpose: "fz-84m repro B — if-arm tail call + per-callsite narrowing; formerly silently dropped the tail-call (overwritten with Goto(join_b, [Var(0)]))"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 2
budget.codegen.instructions: 11
budget.specs.count: 2
budget.planner.worklist_pops: 3
budget.planner.walk_calls: 3
budget.planner.type_fn_calls: 2
budget.planner.matcher_specs: 0
budget.planner.vars: 22
budget.planner.blocks: 4
budget.planner.stmts: 10
budget.planner.dispatches: 1
---

# if_tail_call_in_arm_narrowed

fz-84m repro B — `if` at tail position with a tail-call in one arm.

## History

Before **fz-duq.2**, `lower_if` unconditionally overwrote each arm's
terminator with `Goto(join_b, [arm_value])` even when the arm had
self-terminated via TailCall. The overwrite destroyed the TailCall
and forwarded the sentinel `Var(0)` (the fn's first param) as the
if's value. With per-callsite narrowing here, the planner specialized
`pick(0)` and `pick(1)` and the surviving spec's "result" was `n`
instead of `helper()` or `99` — and downstream inlining + folding
silently dropped the second print entirely, leaving the program to
exit 0 with no output.

After fz-duq.2, each arm body is its own continuation fn. The
then-arm's `helper()` Tail-Returns to the if's caller through the
arm fn's tail-call chain — no clobber.

Expected stdout:

```
7
99
```
