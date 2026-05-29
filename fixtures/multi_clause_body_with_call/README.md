---
purpose: "minimal multi-clause Bug-2 repro — clause body has a Call. Pre-fz-qbg.2 panicked at fz_ir.rs:453; now lowers correctly via the per-clause body cont-fn path"
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

# multi_clause_body_with_call

Minimal repro for the multi-clause class of Bug-2 (fz-g8v) — fz-qbg.2's
test case in fixture form.

## History

Pre-fz-qbg.2: `classify(0)`'s body `helper()` is a tail-position Call,
but the `helper()` lowering as `lower_expr(_, is_tail=true)` doesn't
CPS-split for top-level calls. So this exact program might not have
panicked under the old lowering... but `body_might_cps_split` flags
the call shape as worth wrapping. With fz-qbg.2 it wraps, the clause
body lives in `fn_clause_0`, and TailCall(helper) becomes the cont
fn's terminator.

Expected stdout:

```
7
99
```
