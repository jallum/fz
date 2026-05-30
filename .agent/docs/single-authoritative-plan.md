# Single Authoritative Plan

`compile_with_backend_impl` (`src/ir_codegen/driver.rs`) derives the
specializing plan codegen consumes on IR whose control-flow shape is already
settled. Codegen reads that plan's facts; it does not re-derive them or
reconcile a second codegen plan against the first.

This is the pipeline-level form of the rule in
[`dispatch-as-planner-output.md`](dispatch-as-planner-output.md): dispatch is
planner output, and there is exactly one plan that owns it.

## Pieces

- **`plan_module`** produces the authoritative `ModulePlan`. Every call emits a
  `planner.planned` telemetry event tagged `role: "authoritative"`. A pretyped
  single-module program runs two: the frontend plan and this codegen plan.
- **The shaping plan** is a `ModulePlan` tagged `role: "shaping"` used only to
  drive pre-authoritative CFG simplification (`branch_fold` and `fold`). Its
  facts are discarded before codegen facts are published.
- **`plan_callable_capabilities`** produces a `CapabilityPlan` — each discovered
  spec's `callable_capabilities` plus the per-FnId `fn_effects`, and nothing
  else (no types, call edges, returns, dead branches, or precedence). It emits
  no `planner.planned` event, and the type carries no codegen facts, so it
  cannot stand in for a `ModulePlan`.
- **`discover_specs`** is the shared worklist core: it discovers every reachable
  spec from the entry seeds and runs the effective-return fixpoint. Both
  `plan_module` and `plan_callable_capabilities` build on it.

## Pipeline

```
frontend plan                      # plan_module, authoritative
  → plan_callable_capabilities      # capability slice; no telemetry event
  → rewrite_known_target_closures   # devirtualize known closure calls
  → inline_module_with_plan         # then fuse, reduce, single-use-cont
plan_module(role: "shaping")         # CFG simplification facts only
  → branch_fold, fold, const_bs, dce
plan_module                         # THE authoritative codegen plan
  → lower_destinations              # maintains no plan facts
resolve_module_types → codegen      # consumes the one plan
```

The shaping plan exists because branch folding and ordinary folding consume
planner facts but change block topology. Those changes must happen before the
authoritative codegen plan is built; otherwise `SpecPlan.reachable_blocks` and
`SpecPlan.call_edges` would describe an older body. It still uses the caller's
telemetry handle: production code does not construct `NullTelemetry` to hide
compiler work.

## The pre-plan transforms read a capability slice

`rewrite_known_target_closures` and `inline_module_with_plan` run before the
authoritative plan, because they reshape the call graph it specializes over.
They read only a capability slice:

- **rewrite** reads each spec's `callable_capabilities`, merged to a per-fn
  consensus: a `CallClosure`/`TailCallClosure` whose callee var holds the same
  `KnownFn` in every spec becomes a direct `Call`/`TailCall`.
- **inline** reads `fn_effects` and the `KnownClosure` subset of
  `callable_capabilities` (stateful closures it must not inline away).

So they take a `CapabilityPlan`, not a `ModulePlan`.

Capability precision depends on the return-type fixpoint: a var's callable
capability narrows as its type narrows under return refinement, and the
consensus `KnownFn` that licenses devirtualization holds only when returns are
sharp. So `plan_callable_capabilities` runs the full `discover_specs` worklist
and keeps the capability slice rather than approximating with a cheaper
fixpoint-free pass. What it drops relative to a `ModulePlan` is the module-level
finalization (dead-branch consensus, precedence, the any-key index) and the
telemetry event — facts these transforms do not read. The pass is
interprocedural over the linked working module, which the frontend's per-entry
`_pre_types` is not: `_pre_types` cannot see linked-provider bodies, so a
provider entry param's `KnownFn` capability is visible only here.

## Destination lowering maintains no plan facts

`ir_dest::lower_destinations` desugars `MakeTuple`/`MakeList`/`MakeMap`/
`MapUpdate` into token-linear `Dest*` sequences. It is intra-block, adds no
blocks, and adds no `Call`/`TailCall` edges. It preserves the original
construction *result* var, which the authoritative plan already typed; its only
new SSA names are dest holders and init tokens.

```
{a, b}                       # MakeTuple, result var r : {A, B}
  DestTupleBegin → holder h  # h and tokens: fresh, untyped in the plan
  DestTupleSet h, 0, a
  DestTupleSet h, 1, b
  DestFreeze h → r           # r keeps its plan type
```

Codegen lowers the `Dest*` prims from runtime value bindings, reading plan types
only for the original element/key/value vars (`a`, `b`), never the holders. So
the authoritative plan stays valid for everything codegen reads after lowering,
and no post-destination re-plan is needed.

## Gate this model with

- `cargo test plan_module_called_once_for_shaping_once_for_codegen_in_pipeline --lib`
- `cargo test frontend_to_codegen_pipeline_reports_planner_phase_events --lib`
- `cargo test --test fixture_matrix` — four-path legs plus the dump budgets,
  whose planner metrics key on the `role: "authoritative"` event
- `cargo test --bin fz closure_call_rewritten_to_direct_call rewrite_erases_threaded_constant_closure`
