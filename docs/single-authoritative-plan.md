# Single Authoritative Plan (invariant 1)

`compile_with_backend_impl` (`src/ir_codegen/driver.rs`) derives the
authoritative specializing plan with **one** `plan_module` call, on IR that no
longer changes after that point. There is no invalidate-and-re-derive, no
hand-rolled reconciliation of a second plan against the first, and no
telemetry-silenced intermediate plan.

This is invariant 1 of the planner-as-single-source-of-truth design (see
[`dispatch-as-planner-output.md`](dispatch-as-planner-output.md)): codegen
consumes planner facts; it does not re-derive them.

## The honest plan count

For a pretyped program the pipeline emits exactly **two** `planner.planned`
telemetry events: the frontend plan and the one authoritative codegen plan.
Every `plan_module` call emits one — there is no `NullTelemetry` silencing — and
the call carries a `role: "authoritative"` label so the dump-budget parser keys
the committed plan's shape on it rather than guessing from event order.

Before fz-hfc this read two but ran four: two extra `plan_module` calls
(a pre-transform "run A" and a post-destination "run C") were routed through
`NullTelemetry`, so the count *looked* honest while hiding the redundancy. The
arc made all four visible (the count rose to four), then removed the two
redundant runs (back to two — now truthfully).

## Pipeline (driver.rs)

```
frontend plan (authoritative, counted)
  ↓ plan_callable_capabilities          # capability-only; emits no event
  ↓ rewrite_known_target_closures       # devirtualize known closure calls
  ↓ inline_module_with_plan             # + fuse, reduce, single-use-cont
plan_module  ← THE authoritative plan (authoritative, counted)
  ↓ post-plan folds                     # branch_fold, fold, const_bs, dce
  ↓ lower_destinations                  # maintains no plan facts
resolve_module_types → codegen          # consumes the one plan
```

## The pre-plan transforms read a capability slice, not a plan

`rewrite_known_target_closures` and `inline_module_with_plan` run *before* the
authoritative plan, because they reshape the call graph the plan then specializes
over. They read only a thin slice of planner facts:

- **rewrite** reads each spec's `callable_capabilities`, merged to a per-fn
  consensus: a `CallClosure`/`TailCallClosure` whose callee var holds the same
  `KnownFn` in every spec becomes a direct `Call`/`TailCall`.
- **inline** reads `fn_effects` (a standalone per-fn LFP over the static call
  graph) and the `KnownClosure` subset of `callable_capabilities` (stateful
  closures that must not be inlined away).

So they take a `CapabilityPlan` — each discovered spec's `callable_capabilities`
plus `fn_effects`, and nothing else (no types, call edges, returns, dead
branches, or precedence). A `CapabilityPlan` cannot be used as a codegen plan,
and `plan_callable_capabilities` emits no `planner.planned` event, because it is
not the authoritative plan.

`plan_callable_capabilities` reuses the same spec-discovery worklist as
`plan_module` (the shared `discover_specs` core) rather than a cheaper
fixpoint-free pass. **Capability precision is load-bearing and depends on the
return-type fixpoint**: a var's callable capability narrows as its type narrows
under return refinement, and the consensus `KnownFn` that drives a
devirtualization is lost when returns stay coarse. Skipping the fixpoint was
tried and regresses `apply2`, `enum_sort`, `higher_order`, and
`multi_caller_spec_divergent`. What the capability pass *drops* relative to a
full plan is the module-level finalization (dead-branch consensus, precedence,
the any-key index) and the telemetry event — the authoritative-plan *shape* — not
the worklist the capabilities require. The pass is interprocedural over the
linked working module, which the pretyped frontend's shallow `_pre_types` is not
(it cannot see linked-provider bodies).

## Destination lowering maintains no plan facts

`ir_dest::lower_destinations` desugars `MakeTuple`/`MakeList`/`MakeMap`/
`MapUpdate` into token-linear `Dest*` sequences. It is intra-block, adds no
blocks, adds no `Call`/`TailCall` edges, and preserves the original construction
*result* var (already typed by the authoritative plan). The only new SSA names
are dest-holder and token-threading vars, and codegen lowers the `Dest*` prims
from runtime value bindings — it consults plan types only for the *original*
element/key/value vars, never the holders. So the authoritative plan remains
valid for everything codegen reads after destination lowering; no post-dest
re-plan and no reconciliation loop is needed.
