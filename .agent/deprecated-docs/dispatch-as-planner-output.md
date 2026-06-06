# Dispatch As Planner Output

Dispatch is a planner fact. `ir_planner` decides which target each call site
runs, how that edge returns, what code a callable value names, which blocks are
live, and which bodies are executable. Codegen consumes those facts and lowers
them mechanically; it does not re-derive dispatch from names, source spans,
closure captures, or local type reconstruction.

One rule covers every call shape — source calls, closure calls, continuation
hops, recursive back edges, protocol callbacks, and provider boundaries: the
planner publishes the typed fact; the downstream pass reads it.

This doc is the dispatch contract. See
[`single-authoritative-plan.md`](single-authoritative-plan.md) for the pipeline
rule that codegen consumes the plan it is handed, and
[`destination-passing.md`](destination-passing.md) for init-token destination
construction.

## The Pieces

`ir_planner::plan_module` produces a `ModulePlan`. `materialize_program` then
projects it into a `PlannedProgram` for codegen.

- `SpecPlan` (`fn_types.rs`) is one specialization's local plan. It owns Var
  types (`vars`), block-entry environments (`block_envs`), callable
  capabilities (`callable_capabilities`), selected call edges (`call_edges`),
  reachable blocks (`reachable_blocks`), per-spec dead branches
  (`dead_branches`), closure-entry obligations (`callable_entry_targets`), and
  per-call extern marshal classes (`extern_marshals`).
- `ModulePlan` (`fn_types.rs`) owns the specialization map (`specs`), the
  reachable spec-key set (`reachable_specs`), effective returns
  (`effective_returns`), per-body spec roles (`spec_roles`), the any-key index
  (`any_key_specs`), per-family precedence (`spec_precedence`), per-fn effect
  summaries (`fn_effects`), module-level dead branches (`dead_branches`), and
  per-fn return-shape capabilities (`return_capabilities`).
- `PlannedProgram` (`planned.rs`) is the codegen-facing projection over the
  settled `Module`. It owns stable `SpecId` registration (`spec_registry`,
  `spec_keys`), one `PlannedBody` per registered spec slot (each carrying its
  materialized `SpecPlan`), the callable-entry table, and the finished
  `reachable_specs` set.

The planner consumes `type_infer`'s solved value flow and activation returns; it
does not run a second return-type engine. Names stay narrow where the code is
literally type inference (`type_fn`, `Ty`, `vars`, block environments,
narrowing); a plan is more than its types, so planner names match that broader
scope.

## SpecKey And BodyKey

`SpecKey` is the planner entry key: `fn_id + input + ReturnDemand`. `BodyKey`
drops the demand: `fn_id + input`.

- `effective_returns`, `spec_roles`, and `spec_precedence` are keyed by
  `BodyKey`: a semantic return payload, a reachability justification, and a
  selection precedence are all properties of the `(fn_id, input)` family, not
  of an edge's delivery shape.
- `specs` and `reachable_specs` are keyed by `SpecKey`.

`ReturnDemand` selects an edge's delivery ABI; it does not create a different
value payload. Because demand is part of `SpecKey`, each `SpecKey` registers its
own `SpecId` and gets its own `PlannedBody`: a `tuple_fields` reach and a
`value` reach of one helper are distinct native bodies, exactly like distinct
type specializations. `materialize_program` does not merge them — merging would
force one return ABI onto callers that asked for the other. In the current
corpus a single `BodyKey` is never reached under two different demands, so the
many-`SpecKey`-to-one-`BodyKey` fan-in does not occur; the `BodyKey`-keyed maps
collapse to one entry per spec.

## Activation Projection

`plan_module` reads `type_infer` activation facts as production data and projects
them into planner-visible semantic returns. `ActivationReturnFacts`
(`worklist.rs`) keeps two layers:

- witness activations, keyed by `TypeInferActivationId` (`witness_returns`,
  `witness_public_keys`, observed edges and dead arms per witness) — used for
  callsite-local slot-0 precision, dead-arm proof, and the edge inventory;
- semantic return buckets, keyed by `BodyKey` (`bucket_returns`) — the
  executable contract handed to interpreter and codegen.

`type_infer` keeps unresolved facts as `Pending`/`Unknown`; the planner turns
those into `any` only at this boundary, and only for specs that stay reachable
(`projected_return_for_key`). Unresolved facts are also tracked as overlap
guards (`unsettled_buckets`, keyed by `FnId`). An exact unresolved bucket can be
projected for its own key, but a different known fact is not projected for a
requested key while any unresolved bucket for the same `FnId` overlaps that
domain (`request_overlaps_unsettled`). The guard is key-sensitive: an unsettled
`f(nonempty_list(int))` blocks a broad `f(list(int))` result but leaves disjoint
facts for the same function alone.

`fz.planner.planned` reports the handoff with `type_kernel: "activation"` plus
`activation_return_*` counts (facts, keys, complete/unresolved/invalid entries,
known/unresolved/no-return states, projected returns, projection gaps) and the
`activation_return_projection_gaps` metadata list.

`fz.planner.activation_projection` reports one fact per visible spec, keyed by
`BodyKey` (rendered into the `spec_key` field). It names the spec role,
projection kind (`exact`, `union`, `declared_callable_entry`,
`unsettled_overlap`, `uncovered`), projected return state, final effective
return, covered witness inventory, activation-derived call edges, and
activation-derived dead arms. A projection gap is a reachable spec kept alive
for another contract reason without compatible activation coverage; zero gaps is
the consistency signal.

## Call Edges

`SpecPlan.call_edges` maps a `CallsiteId` to a `CallEdgePlan`. A `CallsiteId`
(`fz_ir`) is `caller FnId + CallsiteIdent + EmitSlot`. The same syntactic call
site can dispatch to different targets in different caller specializations, so a
module-global callsite table is not precise enough — the caller's `SpecKey` is
part of the proof.

`EmitSlot` separates the facts one call-shaped terminator produces:

- `Direct` names the direct callee body.
- `Cont` names the continuation body.
- `ClosureCall` names a closure-call dispatch site.
- `CallableBoundary` names a known local closure value crossing an external or
  provider boundary that may invoke it later.

A `CallEdgePlan` carries a `CallEdgeTarget` and an optional `ReturnContract`.
The target is `Local(SpecKey)` for an in-module body or
`External { target: Mfa, input, demand }` for a provider boundary.

`Cont` edges come from the same map. When the activation kernel observed the
callee input for a callsite, `continuation_key` uses that full callee input
vector as the continuation key before falling back to reconstructing it from
slot 0 plus captures. The observed key refines the input types — it keeps
reducer protocol state such as `{:cont | :halt, ...}` in the continuation ABI
instead of widening slot 0 to a generic type variable. The slot-0 callable
capability still comes from the producing call's result knowledge when that
carries a more precise `KnownFn`/`KnownClosure` fact than the key's first type.

Provider and protocol edges ride the same shape. Before link, an imported edge
is `External`, naming an `Mfa` plus public input and demand. The synthetic
`__external__.*` body that `ir_lower` emits is only a lowering anchor, not a real
body to plan through. `Module::rewrite_external_calls_for_lto` resolves each
`ExternalCallEdge` to a local `FnId` and rewrites the call site in the IR; the
re-planned module then specs it into a `Local` edge.

Stmt-level extern boundaries are intrinsic IR call sites: `Prim::Extern` carries
its own `CallsiteIdent`, so lowering, type inference, planner discovery, and body
materialization all name the same boundary. Matching spans, ordinals, or the
`external_call_edges` side list would be a lossy fallback.

## Return Contracts

A local call edge may carry a `ReturnContract { target: SpecKey, strategy:
ReturnStrategy }`. The target's demand and the strategy's demand must agree
(`ReturnContract::new` asserts it). The strategies are:

- `Value`: ordinary material return.
- `TupleFields(N)`: tuple field delivery to a destructuring continuation.
- `ForwardedDemand(demand)`: a tail-call edge forwards the caller's existing
  demand down the chain.

Ordinary direct calls, tail calls, and continuation hops select `Value`.
`TupleFields` is an explicit ABI capability for callback-style edges and
continuation delivery, granted by `return_context.rs` only when the producer
returns an `N`-tuple on every path (`ReturnCapability::returns_tuple_of_arity`)
and the continuation projects exactly those `N` fields
(`destructures_slot0_into_arity`); it does not rewrite ordinary function
parameters. The delivery axis is `Value` vs `TupleFields` — there is no
list-tail delivery in the data model.

Native return-lane facts follow planned call edges, not raw `FnId` guesses.
`ir_codegen::abi_facts` derives which fns return a boxed `ValueRef` by walking
reachable bodies and their resolved direct, continuation, and tail-call edges,
so a helper clause boxes a scalar at the boundary that actually returns it into
an enclosing continuation.

## Callable Capabilities

`SpecPlan.callable_capabilities` records callable identity as value-capability
data, separate from the runtime object built to represent it:

```text
CallableCapability =
  KnownFn(fn_id)
  KnownClosure { fn_id, captures, capture_capabilities }
  OpaqueCallable
```

- `KnownFn` is a direct code identity with no runtime closure state.
- `KnownClosure` is a direct code identity plus captured runtime state
  (`captures` types and the per-capture `capture_capabilities`).
- `OpaqueCallable` is a callable boundary whose concrete target is not a single
  known function in this plan.

Lowering is the source of the distinction. `ir_lower` emits `Prim::MakeFnRef`
for named function values and zero-capture lambdas, and `Prim::MakeClosure` only
for env-carrying lambdas (`lambda.rs` branches on `captured_vars.is_empty()`).
Codegen enforces the same split: lowering a `MakeClosure` with zero captures
panics, because a thin callable is a `MakeFnRef`. A call-edge fact pairs the
target (what code may run) with the return contract (how that edge returns);
the same capabilities gate lazy continuation representation
([`lazy-continuation-materialization.md`](lazy-continuation-materialization.md)).

## Protocol Dispatch

Protocol implementation selection is planner-owned. From receiver type facts and
visible implementation domains the planner builds a `ProtocolDispatch::Local`
(static-direct), `ProtocolDispatch::External` (provider boundary), or diagnostic
edge.

A finite-union receiver domain is lowered before execution from a
specificity-ordered DispatchMatrix into a `TypeTest`/`If` cascade with a
direct-call outcome per visible local implementation. `narrow` intersects the
receiver with each arm's target type, so when the authoritative plan re-types
the rewritten module each arm's ordinary direct call specs to the right impl. A
closed union needs no fallthrough: the graph's closed residual `Fail` tail lowers
to the final direct `else`. An open or erased receiver keeps the protocol stub
as the final `else`, so a value matching no impl halts with
`:protocol_dispatch_unplanned`. Codegen lowers each `TypeTest` by schema id for
named structs and by value kind for kinded containers such as lists and maps; no
runtime lookup table is emitted.

Protocol callback call sites lower to ordinary call-shaped IR with a protocol
stub callee. The stub is a stable callsite anchor; frontend checking and linking
rewrite it from planner facts.

## Codegen Boundary

Codegen lowers the `PlannedProgram` mechanically by reading planner facts:

- For a direct or continuation call site, codegen reads the selected edge from
  the current caller's `SpecPlan.call_edges`.
- When materialization erased a known zero-capture `CallClosure`, the executable
  body already holds the cloned direct producer and continuation control flow,
  and codegen reads the remapped `call_edges` attached to that `PlannedBody`
  rather than the raw callable value.
- For `Prim::MakeFnRef`/`Prim::MakeClosure`, codegen selects one of the planned
  callable-entry targets for the closure value and reports the choice through
  `fz.codegen.callable_entry_selected`.
- For a return contract, codegen lowers the contract payload it was handed.
- For a registered executable spec, `PlannedProgram::executable_body` resolves
  it to a `PlannedBody`.
- For block liveness, codegen reads `SpecPlan.reachable_blocks`.

Re-walking in codegen would miss per-spec facts, choose a body the spec registry
did not register, or diverge from activation-return projection and continuation
ABI selection; a missing fact is a planner bug.

`materialize_program` prunes each body's `call_edges` to its surviving/remapped
call sites (`materialized_call_edges`). `CallableBoundary` is the only call-edge
fact a terminator slot does not produce, so `materialized_call_edges` keeps it
unconditionally and `materialized_orphan_call_edges` exempts it from the orphan
check. Selective-receive (`ReceiveMatched`) outcome `Cont` edges are
terminator-derived: `materialized_callsite_ids` adds each clause's and the
after-clause's `Cont` callsite to the live set, so they survive as ordinary
materialized callsites, not orphans.

Executable reachability belongs to `PlannedProgram`. `materialized_reachable_specs`
recomputes it from entry seeds by following surviving call edges and live
callable constructions, then retains `Activation`/`CallableEntry` demand
siblings only for body keys that remain reachable — it does not copy
`ModulePlan::reachable_specs` blindly. Known direct-call, tail-direct-call,
closure-call, and tail-closure-call erasure is materializer work too.

## Tests

Semantic reachability and erasure are proven at the planner/materializer layer
on telemetry, before any codegen inspection:

- `fz.planner.planned` / `fz.planner.activation_projection` — activation handoff
  and per-spec projection; zero projection gaps is the consistency signal.
- `fz.planner.materialized` / `fz.planner.body_materialized` — executable bodies;
  `post_plan_reachability_growth_count == 0` and
  `materialized_reachability_missing_body_count == 0` hold,
  `post_plan_reachability_pruned_count` measures pruned specs, and
  `direct_call_inline_count` / `continuation_inline_count` / `fused_block_count`
  measure erasure.
- `fz.codegen.callable_entry_selected` — the closure-entry target codegen chose.

Gate the contract with `cargo test --lib ir_planner`, `cargo test --lib
ir_codegen`, `cargo test --lib
frontend_to_codegen_pipeline_reports_planner_phase_events`, `cargo test --lib
planned_program_materialization_reports_executable_body_folds`, and `cargo test
--test fixture_matrix`.
