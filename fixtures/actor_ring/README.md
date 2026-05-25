---
purpose: "N-hop actor ring with self()-capture + spawn-with-captures + multi-clause CPS-split-in-body; closes fz-g8v by exercising the fz-qbg.2 multi-clause body cont-fn path end-to-end"
paths: [jit, interp, aot]
budget.codegen.functions: 14
budget.codegen.instructions: 284
budget.specs.count: 14
budget.typer.worklist_pops: 28
budget.typer.walk_calls: 28
budget.typer.type_fn_calls: 14
budget.typer.matcher_specs: 0
budget.typer.vars: 78
budget.typer.blocks: 19
budget.typer.stmts: 31
budget.typer.dispatches: 10
---

# actor_ring

N-hop actor ring — each child spawns its successor capturing main's
pid, forwards an incremented token home.

## History

Drafted alongside fz-duq, but blocked: multi-clause `relay/2`'s
terminal clause `relay(0, home) do send(home, receive() + 1) end`
contains `receive()` in a non-tail position (it's an argument to
`+`). The pre-fz-qbg.2 multi-clause lowering shared `try_blocks`
across the source-level fn; the CPS-split triggered by `receive()`
finalized the outer fn while sibling clauses' try-blocks were still
empty → `block_mut` panic at `src/fz_ir.rs:453`.

After fz-qbg.2, `lower_multi_clause` wraps clause bodies that contain
CPS-splits in their own continuation fns (`fn_clause_N`), confining
the split to that clause's lineage. The outer dispatcher is fully
populated (try cascade + arm TailCalls) before any body lowers.

## Notes

Three things exercised together that no other fixture covers:

1. `self()` captured into a closure passed across `spawn`.
2. A process topology built by recursion (depth = N), not by
   hard-coded pids.
3. Multi-clause `relay/2` where one clause body contains a
   non-tail `Receive` (the fz-qbg.2 trigger).

For N=4 the token traverses 5 actors (relay 4 → 3 → 2 → 1 → 0 →
home), each adding 1, so main prints 5.

Listed under `[jit, interp]`; promote to `aot` once a separate pass
confirms parity.
