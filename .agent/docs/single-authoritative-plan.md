# Single Authoritative Plan

Codegen consumes a `ModulePlan`; it never runs the planner. The frontend and the
module pipeline produce the one authoritative plan for the module shape they hand
downstream, and `compile_planned` / `compile_aot_planned` lower that planned
module mechanically.

This is the pipeline-level form of the contract in
[`dispatch-as-planner-output.md`](dispatch-as-planner-output.md): dispatch is
planner output, so downstream passes read selected call targets, reachable
blocks, callable capabilities, and return contracts off the plan instead of
rediscovering them.

## The Pieces

- **`plan_module`** (`ir_planner/worklist.rs`) produces the authoritative
  `ModulePlan` for a settled module and emits `fz.planner.planned` with
  `role: "authoritative"`. The frontend runs it once on the lowered module, and
  `prepare_execution_graph` runs it again on the linked module, so normal source
  execution publishes exactly two authoritative `planned` events.
- **`PreparedExecutionGraph`** (`modules/pipeline.rs`) is the source/runtime
  handoff. It carries the linked `Module` and the `ModulePlan` for that exact
  module. The interpreter and codegen both consume this pair.
- **`compile_planned` / `compile_aot_planned`** (`ir_codegen/mod.rs`) take the
  `ModulePlan` from the caller. The codegen driver performs local,
  invariant-preserving lowering (destination lowering), but it does not change
  call shapes and does not run a second planner pass.
- **`materialize_program`** (`ir_planner/planned.rs`) consumes the supplied
  `ModulePlan` and the settled module to build a `PlannedProgram`: stable
  `SpecId` registration, per-slot plan lookup, executable `PlannedBody` values
  keyed by both `SpecKey` and semantic `BodyKey`, the callable-entry table, and
  the finished `reachable_specs` set.
- **`AbiFacts`** (`ir_codegen/abi_facts.rs`) derives function-level ABI facts
  from the `PlannedProgram`, not raw syntax. It owns the native-fn set
  (`native_fns`), the continuation-fn set (`cont_fns`), the set of fns ever
  named as a call target (`cont_target_fns`), and per-fn closure capture counts
  (`closure_capture_counts`), all read from reachable planned bodies and their
  resolved call edges.

## Pipeline

```text
source frontend / provider linking
  -> plan_module                  # authoritative plan for this module
  -> PreparedExecutionGraph       # module + exact plan
  -> compile_planned
       -> lower_destinations      # local invariant-preserving transform
       -> resolve_module_types    # validates/attaches marshal facts on lowered IR
       -> materialize_program     # executable projection from ModulePlan
       -> AbiFacts::derive
       -> codegen                 # mechanical CLIF lowering
```

LTO mode is the one place that mutates module boundaries on purpose. It erases
the boundaries, runs `plan_module` on the erased module, and hands that fresh
module/plan pair downstream. The pre-erasure plan is discarded.

## What Each Stage Owns And Preserves

`compile_planned` runs the plan-preserving transforms before it lowers, so the
plan it materializes still describes the IR codegen emits.

- **`lower_destinations`** adds destination holders and init tokens. It keeps the
  original result vars and adds no call edges, so reachability and dispatch are
  unchanged. A debug check (`assert_no_new_call_shapes`) holds it to that
  contract.
- **`resolve_module_types`** validates the lowered module and records per-call
  extern marshal facts on each `SpecPlan` (`extern_marshals`); an ascription
  mismatch surfaces as a codegen diagnostic. It does not select dispatch.
- **`materialize_program`** folds and rewrites bodies using facts already in the
  `ModulePlan`. It may erase a proven known call and fuse blocks, then recompute
  reachability over the rewritten graph — but it discovers no new semantic
  reachability.

Two source-lowering choices keep work out of the plan entirely, so the
authoritative plan never has to carry it:

- A direct `dbg(x)` lowers to the `fz_dbg_value(any)` extern effect and returns
  `x` (`ir_lower/expr.rs`), so the plan holds no `Kernel.dbg/1` call edge for
  direct calls.
- Fully static tuple/struct literals can lower to read-only schema-shaped data
  symbols in native codegen (`try_static_struct_literal`). This is a storage
  choice for construction the lowered IR already makes explicit; it adds no call
  edges and no destination facts and leaves the `ModulePlan` untouched.

The observable contract for the whole pipeline: `compile_planned` emits no
`fz.planner.planned` event. The gating test attaches to that event and asserts
codegen adds none beyond the two the frontend and linker already published.
(`materialize_program` still emits its own `fz.planner.body_materialized` and
`fz.planner.materialized` events — those report the projection, not a replan.)

## Materializing The Planned Program

`PlannedProgram` is the handoff between planner/fold and codegen. It preserves
the registry invariant that an any-key `SpecId.0 == FnId.0`, reserving slots
where needed, and exposes executable bodies as `PlannedBody` values that carry
both the exact `SpecKey` and its semantic `BodyKey`. Lowering a reachable
registered executable spec always finds its body by construction
(`executable_body`).

`ReturnDemand` is part of `SpecKey` identity and selects an edge's delivery ABI
(`ReturnDelivery::Value` or `TupleFields(n)`); it is not a distinct return
payload. `BodyKey` drops the demand, so demand siblings share `BodyKey`-level
return facts yet stay separate materialized bodies — merging them would force one
return ABI onto callers that asked for the other.

`AbiFacts::derive` reads dispatch off the planned call edges on those bodies.
Continuation and direct-call `SpecId`s come from `SpecPlan.call_edges`; return
representations then propagate through continuation chains and resolved tail-call
edges. Codegen resolves a target through that edge, never by assuming a raw
`FnId` maps to the executable spec it wants. ABI-contract telemetry covers only
reachable executable specs, not the sentinel slots kept to hold a stable
`SpecId`.

### Inlining known calls

While materializing a body, `inline_single_entry_direct_calls` may erase a
proven local direct call, tail direct call, known zero-capture closure call, or
known zero-capture tail closure call. The callee's effects must be inline-safe
(no allocation, observable effect, allocation-stat read, scheduler visibility,
halt, or opaque call) per `direct_callee_is_inline_safe`.

- A **non-tail call** clones the selected producer return graph and the selected
  continuation graph into the caller, so it requires both call edges in the
  caller `SpecPlan`. Producer `Return` becomes a `Goto` into the cloned
  continuation entry.
- A **tail call** clones only the selected producer return graph and rewrites
  producer `Return` edges to the caller's `Return`.

Cloned call edges are remapped from the moved fn's `FnId` onto the materialized
caller (`add_remapped_call_edges`). A continuation that carries physical
params/capabilities moves only when it is a statement-free transport graph
(`continuation_graph_can_move_into_caller`).

### Fusing and retyping

After a rewrite, `fuse_single_predecessor_goto_blocks` folds a `Goto` into a
closed single-predecessor target; if the target's params are read by successor
blocks, the block stays in place. Whenever materialization removes blocks, the
body is retyped (`retype_materialized_body`) so `PlannedBody.spec_plan` matches
the executable body.

### Reachability over the rewritten graph

`materialized_reachable_specs` reseeds from entry specs, follows surviving
materialized call edges and live callable constructions, and re-adds
activation/callable-entry role siblings only for body keys that stay reachable.

### Telemetry and the consistency harness

Each body emits `fz.planner.body_materialized` (including `spec_id`, `fn_id`,
`fold/inline/fuse counts`, and `orphan_call_edge_count`). The aggregate
`fz.planner.materialized` reports spec slots, executable body count, sentinel
slots, fold/rewrite counts, reachable specs, `post_plan_reachability_growth_count`,
`post_plan_reachability_pruned_count`, `materialized_reachability_missing_body_count`,
and `make_closure_callable_gap_count`.

`authoritative_planner_consistency_issues` reads those events and requires every
materialized body to report zero orphan call edges (after accounting for
callable-boundary and selective-receive `Cont` outcomes), zero make-closure
callable gaps, zero post-plan reachability growth, and zero missing bodies.
Pruning is allowed and only measured: a rewrite that erases edges may shrink
reachability.

## Callable Entries And Static Singletons

A semantic body spec and its public callable entry are distinct executable
things:

- the **planned body** is the direct typed entry for a reachable semantic
  `BodyKey`;
- the **callable entry** is the generic closure-call entry for that body, with a
  `(args..., self, cont)` Tail-CC signature.

Closure values store callable entries for indirect calls. Direct calls may target
typed planned bodies when the planner selected that exact local target. Codegen
lowers `Prim::MakeFnRef` through the callable-entry contract directly;
`Prim::MakeClosure` is the env-carrying path and errors at codegen if it reaches
with zero captures.

Callable-entry selection is site-specific. `PlannedProgram` keeps the
callable-entry targets the planner proved (`callable_entry_targets`), and codegen
lowers each `MakeFnRef` / env-carrying `MakeClosure` through the matching target
for that statement's typed environment (`select_callable_entry_target`). The
selected entry is observable through `fz.codegen.callable_entry_selected`.

Static closure singletons are keyed by the spec slot (`cl_sid`) codegen passes to
`fz_get_static_closure`. `collect_static_closure_targets` populates that table
with every zero-capture callable entry plus every zero-capture closure-shaped
reachable spec used as a direct native `self` argument — a zero-capture singleton
ignores `self`, so one singleton serves any direct-call site for that fn.
Callable-entry ids are therefore a subset of static-singleton ids.

## Tiny Walkthrough

```text
fn main(), do: dbg(42)
  frontend: lower + plan_module        -> authoritative "planned" event #1
  prepare_execution_graph: plan_module -> authoritative "planned" event #2
  compile_planned(module, plan):
    lower_destinations / resolve_module_types   # plan-preserving
    materialize_program(plan)                   # body_materialized + materialized
    AbiFacts::derive(plan)                       # ABI off planned edges
    codegen                                      # CLIF; no "planned" event
```

## Gate This Model With

- `cargo test --lib ir_codegen::tests::codegen_pipeline_reports_only_one_authoritative_plan -- --nocapture`
- `cargo test --lib ir_codegen::tests::frontend_to_codegen_pipeline_reports_planner_phase_events -- --nocapture`
- `cargo test --lib ir_codegen::tests::tail_call_closure_reuses_frame_via_count_loop -- --nocapture`
- `cargo test --test fixture_matrix`
