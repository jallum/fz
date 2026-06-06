# Single Authoritative Plan

Codegen consumes a `ModulePlan`; it never runs the planner. The frontend and the
module pipeline produce the one authoritative plan for the module shape they hand
downstream, and `Compiler` (`src/compiler.rs`) is the production driver that
threads that planned module through execution-graph preparation, native
preflight, and backend emission.

This is the pipeline-level form of the contract in
[`dispatch-as-planner-output.md`](dispatch-as-planner-output.md): dispatch is
planner output, so downstream passes read selected call targets, reachable
blocks, callable capabilities, and return contracts off the plan instead of
rediscovering them.

## The Pieces

- **`plan_module_with_role`** (`ir_planner/worklist.rs`) produces the
  `ModulePlan` for a settled module and emits `fz.planner.planned` with the
  caller-supplied `role`. The production source pipeline uses
  `role: "frontend_check"` on the lowered source module and
  `role: "linked_execution_graph"` on the linked runtime module; LTO and
  artifact materialization use distinct role names for their own replans.
- **`compiler::World`** (`src/compiler.rs`) is the authoritative mutable state
  carrier for production callers. It owns the settled linked `Module`, its
  exact `ModulePlan`, diagnostics/source-map state, linked units, and the
  native-preparation facts derived from that same module/plan pair. Its
  execution-image accessors are named `linked_module()` /
  `linked_module_plan()` to distinguish that linked whole-program IR image from
  source-language `defmodule` boundaries.
- **`Compiler`** (`src/compiler.rs`) is the stage owner for production callers.
  It drives source/program frontend work into a mutable `World`, prepares the
  execution graph through `modules::pipeline`, enriches the same `World` with
  native-preparation facts, and then selects the JIT or AOT backend.
- **`compile_planned` / `compile_aot_planned`** (`ir_codegen/mod.rs`) take the
  `ModulePlan` from the caller. They remain as lower-level convenience wrappers
  for tests and helper code, but the production CLI/REPL path reaches native
  emission through `Compiler`.
- **`prepare_preplanned_native` / `compile_with_backend_prepared`**
  (`ir_codegen/driver.rs`, wrapped by `Compiler`) are the native-preparation and
  backend-emission mechanics. Production callers reach them only through
  `Compiler`, which caches the prepared-native state on `World`.
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
  -> plan_module_with_role          # exact plan for this module shape
  -> compiler::World                # linked module + exact plan + diagnostics
  -> Compiler::prepare_native_program(world)
       -> lower_destinations        # local invariant-preserving transform
       -> resolve_module_types      # validates/attaches marshal facts on lowered IR
       -> materialize_program       # executable projection from ModulePlan
       -> AbiFacts::derive
  -> Compiler::compile_planned / compile_aot_planned
       -> codegen backend emission  # mechanical CLIF lowering
```

LTO mode is the one place that mutates module boundaries on purpose. It erases
the boundaries, runs `plan_module_with_role` on the erased module, and hands
that fresh module/plan pair downstream. The pre-erasure plan is discarded.

## What Each Stage Owns And Preserves

`Compiler::prepare_native_program` runs the plan-preserving transforms before
native emission and caches the result on `World`, so the plan it materializes
still describes the IR codegen emits.

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

The observable contract for the whole pipeline: native compilation emits no new
`fz.planner.planned` event. The gating tests attach to that event and assert the
Compiler-driven native path adds none beyond the caller-owned planning passes
that already published the `frontend_check` / `linked_execution_graph` (or
corresponding LTO/materialization) roles. (`materialize_program` still emits
its own `fz.planner.body_materialized` and `fz.planner.materialized` events —
those report the projection, not a replan.)

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
Zero-capture callable-entry ids are therefore a subset of static-singleton ids; a
capturing callable entry (`capture_count > 0`) is not a static singleton, because
its env must be built per construction.

## Tiny Walkthrough

```text
fn main(), do: dbg(42)
  frontend: lower + plan_module        -> authoritative "planned" event #1
  prepare_execution_graph: plan_module -> authoritative "planned" event #2
  Compiler::prepare_native_program(world):
    lower_destinations / resolve_module_types   # plan-preserving
    materialize_program(plan)                   # body_materialized + materialized
    AbiFacts::derive(plan)                       # ABI off planned edges
  Compiler::compile_planned(module, plan):
    codegen                                      # CLIF; no "planned" event
```

## Gate This Model With

- `cargo test --lib codegen_pipeline_reports_frontend_and_linked_plans -- --nocapture`
- `cargo test --lib ir_codegen::tests::frontend_to_codegen_pipeline_reports_planner_phase_events -- --nocapture`
- `cargo test --lib ir_codegen::tests::tail_call_closure_reuses_frame_via_count_loop -- --nocapture`
- `cargo test --test fixture_matrix`
