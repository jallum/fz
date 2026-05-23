---
purpose: "minimal multi-clause Bug-2 repro — clause body has a Call. Pre-fz-qbg.2 panicked at fz_ir.rs:453; now lowers correctly via the per-clause body cont-fn path"
paths: [jit, interp, aot]
budget.codegen.functions: 3
budget.codegen.instructions: 13
budget.specs.count: 3
budget.typer.worklist_pops: 6
budget.typer.walk_calls: 6
budget.typer.type_fn_calls: 3
budget.typer.matcher_specs: 0
budget.typer.vars: 29
budget.typer.blocks: 7
budget.typer.stmts: 12
budget.typer.dispatches: 2
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
