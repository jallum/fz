---
purpose: "fz-84m repro A — constant cond + non-tail call in if-arm; formerly panicked at fz_ir.rs:453 ('unknown block') because then-arm's CPS-split finalized the outer fn while else_b was still empty"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 8
budget.specs.count: 1
budget.typer.worklist_pops: 1
budget.typer.walk_calls: 1
budget.typer.type_fn_calls: 1
budget.typer.matcher_specs: 0
budget.typer.vars: 15
budget.typer.blocks: 3
budget.typer.stmts: 6
budget.typer.dispatches: 0
---

# if_constant_cond_with_call

fz-84m repro A — constant cond + non-tail call in if-arm.

## History

Before **fz-duq.2**, this program panicked during IR construction at
`block_mut` (src/fz_ir.rs:453, "unknown block"). The then-arm's
`print(helper())` lowered as a non-tail Call inside print's args,
triggering `cps_split_call` which finalized the outer fn. The
subsequent switch to else_b (a BlockId in the now-built fn) corrupted
the lowering.

After fz-duq.2, each if-arm body lives in its own continuation fn
(`if_then` / `if_else`); CPS-splits in arm bodies are confined to
that arm's lineage. The outer fn is fully populated (just `Term::If`
+ two arm TailCalls) before any arm body lowers.

Expected stdout: `99`.
