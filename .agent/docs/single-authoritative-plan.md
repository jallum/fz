# Single Authoritative Plan

Codegen consumes a `ModulePlan`; it does not run the planner. The frontend and
module pipeline produce the authoritative plan for the module shape they hand to
downstream engines, and `compile_planned` / `compile_aot_planned` lower that
planned module mechanically.

This is the pipeline-level form of the rule in
[`dispatch-as-planner-output.md`](dispatch-as-planner-output.md): dispatch is
planner output, and downstream passes do not rediscover selected call targets,
reachable blocks, callable capabilities, or return contracts.

## Pieces

- **`plan_module`** produces the authoritative `ModulePlan` for a settled
  module. Each call emits `fz.planner.planned` with `role: "authoritative"`.
  Normal source execution publishes one frontend plan and one linked-module
  plan; planned codegen publishes no additional planner event.
- **`PreparedExecutionGraph`** is the source/runtime handoff. It contains the
  linked `Module` and the `ModulePlan` for that exact module. Interp and codegen
  consume this pair.
- **`compile_planned` / `compile_aot_planned`** require the caller to provide
  the `ModulePlan`. The codegen driver may perform local, invariant-preserving
  lowering such as destination lowering, but it must not change call shapes or
  run a second planner pass to explain its edits.
- **`materialize_program`** consumes the supplied `ModulePlan` and the settled
  module to produce a `PlannedProgram`: stable `SpecId` registration, per-slot
  plan lookup, executable `PlannedBody` values shared by semantic `BodyKey`,
  callable entries, and the finished `reachable_specs` set.
- **`AbiFacts`** derives codegen ABI facts from the `PlannedProgram`, not raw
  syntax. These facts decide which functions use native ABIs, continuation ABIs,
  closure-shaped self parameters, and direct callable targets.

## Pipeline

```text
source frontend / provider linking
  -> plan_module                  # authoritative plan for this module
  -> PreparedExecutionGraph       # module + exact plan
  -> compile_planned
       -> lower_destinations      # local invariant-preserving transform
       -> resolve_module_types    # validates/coheres type facts on lowered IR
       -> materialize_program     # executable projection from ModulePlan
       -> AbiFacts::derive
       -> codegen                 # mechanical CLIF lowering
```

LTO mode is the exception that intentionally mutates module boundaries. It
erases boundaries, then runs `plan_module` for the erased module and hands that
new exact pair downstream. The discarded pre-erasure plan is not used by
codegen.

## Invariants

- Codegen emits no `fz.planner.planned` event. A test that observes an
  authoritative planner event during `compile_planned` is catching a regression.
- A transform that changes call shapes or reachability must either happen
  before the authoritative plan or maintain the existing plan facts by
  construction. Replanning after the transform is not an acceptable repair.
- Destination lowering may add destination holders and init tokens, but it must
  preserve the original result vars and must not add call edges.
- `resolve_module_types` may validate and attach local marshal/coercion facts
  for the lowered module; it does not own dispatch.
- Planned body materialization may fold a body using facts already present in
  the `ModulePlan`; it must not discover new semantic reachability.

## Planned Program Materialization

`PlannedProgram` is the handoff between planner/fold and codegen. It preserves
the registry invariant that any-key `SpecId.0 == FnId.0`, including reserved
slots where needed, but exposes executable bodies as `PlannedBody` values keyed
by semantic `BodyKey` rather than one body per `SpecKey` slot. If codegen is
lowering a registered executable spec, the matching body exists by construction.

`ReturnDemand` can select an edge ABI, but it is not a distinct semantic return
payload and does not justify a second executable body. Multiple compatible
`SpecKey` slots may resolve to the same `PlannedBody`.

Per-spec folds run while materializing the planned program, not ad hoc inside
the Cranelift lowering loop. Each body emits
`fz.planner.body_materialized`, including its `spec_id`, `fn_id`,
`folded_prim_count`, and `folded_branch_count`. The aggregate event
`fz.planner.materialized` reports spec slots, executable body count, sentinel
slots, fold counts, reachable specs, and `post_plan_reachability_growth_count`.
The consistency harness requires post-plan reachability growth to stay `0`.

## Callable Entries And Static Singletons

A semantic body spec and its public callable entry are distinct executable
things:

- the **planned body** is the direct typed entry for a reachable semantic
  `BodyKey`;
- the **callable entry** is the generic closure-call entry for that body.

Closure values store callable entries for indirect calls. Direct calls may
target typed planned bodies when the planner selected that exact local target.
Codegen lowers `Prim::MakeFnRef` through that callable-entry contract directly;
`Prim::MakeClosure` is now the env-carrying path only.

Static closure singletons are keyed by the spec slot (`cl_sid`) that codegen
passes to `fz_get_static_closure`. The singleton table must include every
zero-capture callable entry and every zero-capture closure-shaped reachable spec
used as a direct native self argument. Callable-entry ids are therefore a subset
of static singleton ids, not the whole set.

## Gate This Model With

- `cargo test --lib ir_codegen::tests::codegen_pipeline_reports_only_one_authoritative_plan -- --nocapture`
- `cargo test --lib ir_codegen::tests::frontend_to_codegen_pipeline_reports_planner_phase_events -- --nocapture`
- `cargo test --lib ir_codegen::tests::runtime_enumerable_list_reduce_reports_low_level_done_and_halt -- --nocapture`
- `cargo test --lib ir_codegen::tests::tail_call_closure_reuses_frame_via_count_loop -- --nocapture`
- `cargo test --test fixture_matrix`
