---
purpose: "fz-uwq.4 regression — divergent dispatch across two caller specs of the same higher-order fn"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 10
budget.specs.count: 3
budget.planner.worklist_pops: 3
budget.planner.walk_calls: 3
budget.planner.type_fn_calls: 3
budget.planner.matcher_specs: 0
budget.planner.vars: 17
budget.planner.blocks: 3
budget.planner.stmts: 10
budget.planner.dispatches: 0
---

# multi_caller_spec_divergent

`route(f, n)` is invoked at two source sites with two distinct
closure literals: the named fn `id` and the inline lambda
`fn(x) -> x * 2`. The planner mints two specs of `route` — one per
`f` — whose single inner `f.(n)` callsite dispatches to two
different targets.

The shape collapses if dispatch information is keyed only by
spec-agnostic `CallsiteId` (one entry per source-position callsite,
last-write-wins across specs). Today's pipeline gets the right
answer because per-spec fold + per-spec body codegen each resolve
their own dispatch independently — `module.callsite_outcomes` isn't
on the path that decides this specific call. fz-uwq.5+ migrates
those reads through `SpecPlan.dispatches`, which is *per-spec* by
construction. This fixture pins down the correct behavior so a
future migration regression can't slip through silently.

Worked through in `.agent/docs/dispatch-as-planner-output.md` (Worry 2).
