---
purpose: "fz-uwq.4 regression — divergent dispatch across two caller specs of the same higher-order fn"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 2
budget.codegen.instructions: 9
budget.specs.count: 4
budget.typer.worklist_pops: 5
budget.typer.walk_calls: 5
budget.typer.type_fn_calls: 4
budget.typer.matcher_specs: 0
budget.typer.vars: 22
budget.typer.blocks: 6
budget.typer.stmts: 12
budget.typer.dispatches: 2
---

# multi_caller_spec_divergent

`route(f, n)` is invoked at two source sites with two distinct
closure literals: the named fn `id` and the inline lambda
`fn(x) -> x * 2`. The typer mints two specs of `route` — one per
`f` — whose single inner `f(n)` callsite dispatches to two
different targets.

The shape collapses if dispatch information is keyed only by
spec-agnostic `CallsiteId` (one entry per source-position callsite,
last-write-wins across specs). Today's pipeline gets the right
answer because per-spec fold + per-spec body codegen each resolve
their own dispatch independently — `module.callsite_outcomes` isn't
on the path that decides this specific call. fz-uwq.5+ migrates
those reads through `FnTypes.dispatches`, which is *per-spec* by
construction. This fixture pins down the correct behavior so a
future migration regression can't slip through silently.

Worked through in `docs/dispatch-as-typer-output.md` (Worry 2).
