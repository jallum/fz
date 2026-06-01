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
- **`materialize_program`** consumes the authoritative `ModulePlan` plus the
  settled `Module` and produces a `PlannedProgram`: stable `SpecId`
  registration, per-spec plan lookup, and executable per-spec bodies. A
  `PlannedBody` is always executable; reserved `SpecId` slots are slot metadata,
  not optional bodies. The pass emits `fz.planner.materialized` with body and
  fold counters.
- **Frontend protocol rewrites** apply only static-single protocol callsites:
  the same physical `CallsiteId` must select the same local target in every
  reachable caller specialization. Conflicting protocol targets are left as
  protocol stubs until closed-union switch dispatch rewrites them into
  `TypeTest` / `If` cascades. This preserves one shared IR body while still
  honoring per-spec protocol facts.
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
resolve_module_types
  → materialize_program             # executable projection from ModulePlan
  → codegen                         # lowers planned bodies mechanically
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

## Planned Program Materialization

`PlannedProgram` is the handoff between planner/fold and codegen. It preserves
the registry invariant that any-key `SpecId.0 == FnId.0`, including reserved
slots where needed, but exposes executable bodies as `PlannedBody` values rather
than `Option<FnIr>`. If codegen is lowering a registered spec, the matching body
exists by construction.

Per-spec folds run while materializing the planned program, not ad hoc inside
the Cranelift lowering loop. Each body emits
`fz.planner.body_materialized`, including its `spec_id`, `fn_id`,
`folded_prim_count`, and `folded_branch_count`. The aggregate event
`fz.planner.materialized` reports:

- `spec_slot_count`: every slot in the SpecId-indexed registry, including
  reserved slots.
- `planned_body_count`: executable bodies materialized for registered specs.
- `sentinel_spec_count`: reserved slots with no executable spec.
- `folded_prim_count` and `folded_branch_count`: per-spec folds applied while
  building planned bodies.

## Gate this model with

- `cargo test plan_module_called_once_for_shaping_once_for_codegen_in_pipeline --lib`
- `cargo test frontend_to_codegen_pipeline_reports_planner_phase_events --lib`
- `cargo test planned_program_materialization_reports_executable_body_folds --lib`
- `cargo test --test fixture_matrix` — four-path legs plus the dump budgets,
  whose planner metrics key on the `role: "authoritative"` event
- `cargo test --bin fz closure_call_rewritten_to_direct_call rewrite_erases_threaded_constant_closure`
