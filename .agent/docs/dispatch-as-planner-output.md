# Dispatch As Planner Output

Dispatch is a planner fact. Codegen consumes selected targets, return
contracts, callable capabilities, reachable blocks, and materialized bodies; it
does not rediscover those facts from names, source spans, closure captures, or
local type reconstruction.

The same ownership rule applies to source calls, closure calls, continuation
hops, recursive back edges, protocol callbacks, provider boundaries, and
scheduler-visible boundaries: the planner publishes the typed fact, downstream
passes mechanically lower it.

This doc is the planner-facing dispatch contract. See
[`single-authoritative-plan.md`](single-authoritative-plan.md) for the pipeline
rule that codegen consumes the authoritative plan it is handed, and
[`destination-passing.md`](destination-passing.md) for local init-token
destination construction.

## Planner Vocabulary

`ir_planner::plan_module` produces the authoritative `ModulePlan`.

- `SpecPlan` is one specialization's local plan. It owns Var and block-entry
  types, callable capabilities, selected call edges, reachable blocks,
  per-spec dead branches, extern marshal facts, and callable-entry obligations.
- `ModulePlan` owns the specialization map, reachable spec keys, effective
  returns, spec roles, any-key indexes, precedence, effect summaries,
  module-level dead branches, and no test-only witness artifacts.
- `PlannedProgram` is the codegen-facing projection over the settled `Module`.
  It owns stable `SpecId` registration, per-slot `SpecPlan` references,
  executable `PlannedBody` values, callable entries, and the finished
  `reachable_specs` set.

Local type-inference vocabulary stays narrow where the code is literally type
inference: `type_fn`, `Ty`, `vars`, block environments, narrowing, and concrete
type helpers. A plan is more than the types it carries; planner names match
that broader scope.

## SpecKey And BodyKey

`SpecKey` and `BodyKey` are intentionally different.

- `SpecKey` is the public planner entry key: `FnId + input + ReturnDemand`.
- `BodyKey` is the semantic body key: `FnId + input`.
- Effective returns are keyed by `BodyKey`.
- Materialized executable bodies are keyed by `BodyKey`.
- Multiple compatible `SpecKey` slots may resolve to the same `PlannedBody`.

`ReturnDemand` can select an edge ABI, but it is not a distinct semantic return
payload and does not justify a second executable body. A value-return activation
fact covers every compatible demand for the same `BodyKey`; the planner must
not run a separate return-type engine to fill demand siblings.

When two `SpecKey` slots share a `BodyKey`, their `SpecPlan`s must be
interchangeable: the body interior, the outgoing call edges, the closure-entry
obligations, and the extern marshal classes are all body-level facts, not
edge-ABI facts. `materialize_program` emits
`fz.planner.body_plan_sibling_consistency` per shared-body comparison and rolls
any divergence up onto `fz.planner.materialized`
(`sibling_body_plan_divergence_count`); the authoritative consistency gate fails
if any sibling diverges. In the current corpus the shared-body path is not
exercised at all — demand siblings of one `BodyKey` do not arise in practice —
so the gate holds vacuously and stands ready if that ever changes.

## Activation Projection

`plan_module` reads structured `type_infer` activation facts as production
data and projects them into planner-visible semantic bodies. This is data flow,
not telemetry scraping.

The planner keeps two layers:

- witness activations keyed by activation id, for callsite-local slot-0
  precision, dead-arm proof, and edge inventory;
- semantic return buckets keyed by `BodyKey`, for the executable contract
  handed to interpreter and codegen.

Unresolved activation facts are retained both as exact boundary facts and as
overlap guards. An exact unresolved semantic bucket can be projected at the
final boundary (`Pending`/`Unknown` erase to `any` there), but a different
known fact is not projected for a requested key when any unresolved bucket for
the same `FnId` overlaps that requested domain. The guard is key-sensitive:
unsettled `f(nonempty_list(int))` blocks a broad `f(list(int))` result, but it
does not poison disjoint facts for the same function.

`fz.planner.planned` reports the activation handoff with `type_kernel:
"activation"` plus activation fact/key counts, entry
completion/unresolved/invalid counts, known/unresolved/no-return counts,
projected return count, projection-gap count, and
`activation_return_projection_gaps`.

`fz.planner.activation_projection` reports the same boundary per visible spec.
It names the planner `SpecKey`, `BodyKey`, spec role, projection kind,
projected return state, final effective return, covered witness inventory,
activation-derived call edges, and activation-derived dead arms.

Projection gaps are not alternate planner-side return analysis. They are
reachable specs kept alive for another contract reason without compatible
activation coverage. Zero projection gaps is the consistency signal.

## Call Edges

`SpecPlan.call_edges` is keyed by `CallsiteId`: `(caller FnId, intrinsic
CallsiteIdent, EmitSlot)`. A `CallEdgePlan` names the selected target and the
return contract for that exact caller specialization.

`EmitSlot` separates the facts produced by one call-shaped terminator:

- `Direct` names the direct callee body.
- `Cont` names the continuation body.
- `ClosureCall` names a closure-call dispatch site.
- `CallableBoundary` names a known local closure value crossing an external or
  provider boundary that may invoke it later.

The same syntactic callsite can dispatch to different targets in different
caller specializations, so a module-global callsite table is not precise
enough. The current caller `SpecKey` is part of the proof.

Continuation `Cont` edges are selected from the same call-edge map. When the
activation kernel observed the callee input for a callsite, the planner uses
that full callee input vector as the continuation key before falling back to
local reconstruction from captures. This keeps reducer protocol state such as
`{:cont | :halt, ...}` in the continuation ABI instead of widening slot 0 to a
generic type variable. The observed key refines the input types; slot-0
callable capability still comes from result knowledge when that carries a more
precise `KnownFn` / `KnownClosure` fact than the public callable surface.

Provider-boundary and protocol targets ride the same call-edge shape. Before
link, an imported call edge names an `ExportKey` plus public input and demand.
Linking remaps ids and resolves that boundary edge to a local `SpecKey` in the
same transformation that rewrites the IR. The synthetic `__external__.*` stub is
only a lowering anchor; the planner must not plan through it as a real body.

Stmt-level extern boundaries are intrinsic IR callsites. `Prim::Extern` carries
its own `CallsiteIdent`, so lowering, type inference, planner discovery, and
body materialization all talk about the same boundary fact. Matching spans,
ordinals, or `external_call_edges` is a lossy fallback and not a valid planner
source.

## Return Contracts

A local call edge may carry a `ReturnContract`:

```text
ReturnContract {
  target: SpecKey,
  strategy: ReturnStrategy,
}
```

The target demand and strategy demand must agree. Current executable strategies
are:

- `Value`: ordinary material return.
- `TupleFields(N)`: tuple field delivery to a continuation.
- `ForwardedDemand(demand)`: a tail-call edge forwards the caller's existing
  demand.

The active planner path for ordinary direct calls, tail calls, and continuation
hops selects `Value`. Tuple-field demand remains an explicit ABI capability for
callback-style edges and continuation delivery; it does not rewrite ordinary
function parameters. There is no list-tail return-delivery axis in the data
model.

Native return-lane facts follow planned call edges, not raw `FnId` guesses.
When a `ValueRef` return is required by an enclosing continuation, the ABI
planner propagates that requirement through continuation chains and down
resolved tail-call edges so helper clauses box scalar returns at the boundary
that actually returns them.

If destination-style return delivery comes back, it must come back as explicit
planner-authored adapter or entry facts with telemetry and consistency checks.
Codegen must not probe for alternate spec bodies, inspect continuation
captures, or synthesize extra destination arguments.

## Callable Capabilities

`SpecPlan.callable_capabilities` carries callable identity as value-capability
data:

```text
CallableCapability =
  KnownFn(fn_id)
  KnownClosure { fn_id, captures }
  OpaqueCallable
```

The names describe what the compiler knows about a value, not which runtime
object must be built:

- `KnownFn` is a direct code identity with no runtime closure state.
- `KnownClosure` is a direct code identity plus captured runtime state.
- `OpaqueCallable` is a callable boundary whose concrete target is not a
  single known function in this plan.

Lowering is the semantic source of that distinction. `ir_lower` now emits
`Prim::MakeFnRef` for named function values and zero-capture lambdas, and
`Prim::MakeClosure` only for env-carrying lambdas. Downstream phases may still
choose a compatible runtime representation, but they must not recover
`KnownFn` by reinterpreting `MakeClosure(..., [])` as a thin callable because
that IR shape is no longer the source truth.

Call-edge facts consume callable capabilities alongside the return contract:
the target says what code may run, and the return contract says how that edge
returns. The same facts gate lazy continuation representation; see
[`lazy-continuation-materialization.md`](lazy-continuation-materialization.md).
A threaded callable parameter can be rewritten to a direct zero-capture
function only when every specialization of the enclosing function that has a
callable fact agrees on the same `KnownFn`. `KnownClosure` and
`OpaqueCallable` are positive evidence that runtime callable state may exist,
so they poison the consensus.

## Protocol Dispatch

Protocol implementation selection is planner-owned dispatch. The planner
selects a static-direct (`ProtocolDispatch::Local`), provider-boundary
(`ProtocolDispatch::External`), or diagnostic edge from receiver type facts and
visible implementation-domain facts.

Finite-union receiver domains are rewritten before execution into `TypeTest` /
`If` cascades with direct-call arms for each visible local implementation.
Named source structs are tested by schema id, and kinded containers such as
lists and maps are tested by value kind. Open or erased receiver domains keep a
final protocol-stub fallthrough for any residual non-implementing shape; no
runtime lookup table is emitted.

Protocol callback callsites lower to ordinary call-shaped IR with a protocol
stub callee. The stub is a stable callsite anchor, not the semantic target.
Frontend checking and linking rewrite it using planner facts rather than
rediscovering protocol targets downstream.

## Codegen Boundary

Codegen lowers the `PlannedProgram` mechanically.

- If codegen sees a direct or continuation callsite, the current caller's
  `SpecPlan.call_edges` must contain the selected edge.
- If materialization erased a known zero-capture `CallClosure`, the executable
  body already contains the cloned direct producer and continuation control
  flow. Codegen consumes the remapped `SpecPlan.call_edges` attached to that
  `PlannedBody`; it must not rediscover the closure target from the raw
  callable value.
- Materialized `SpecPlan.call_edges` are pruned to surviving/remapped body
  callsites. `CallableBoundary` edges and selective-receive outcome `Cont`
  edges are representation/reachability obligations rather than ordinary
  terminator slots, so the orphan-edge check classifies them separately.
- If codegen lowers `Prim::MakeFnRef` or `Prim::MakeClosure`, the current
  statement site must select one of the planned callable-entry targets for
  that closure value. The selected entry is reported through
  `fz.codegen.callable_entry_selected`.
- If codegen lowers a return contract, it must lower the contract payload it
  was handed.
- If codegen lowers a registered executable spec, `PlannedProgram` must resolve
  it to a `PlannedBody`.
- If codegen decides whether a block is live, it reads
  `SpecPlan.reachable_blocks`.

Missing facts are compiler bugs. Re-walking in codegen is wrong because it can
miss per-spec facts, choose a body the `SpecRegistry` did not register, or
silently diverge from activation-return projection and continuation ABI
selection.

Executable spec reachability belongs to `PlannedProgram`. Tests that prove a
spec is semantically reachable live with planner/materializer coverage and
observe `fz.planner.materialized` or `fz.planner.body_materialized` telemetry.
Known direct-call and closure-call erasure is also materializer coverage:
tests observe `direct_call_inline_count`, `continuation_inline_count`, and
`fused_block_count` before inspecting codegen output.
Codegen tests assert mechanical lowering effects for bodies the planned program
already selected.

## Gates

Use these gates when changing this contract:

- `cargo test --lib ir_planner`
- `cargo test --lib ir_codegen`
- `cargo test --lib frontend_to_codegen_pipeline_reports_planner_phase_events`
- `cargo test --lib planned_program_materialization_reports_executable_body_folds`
- `cargo test --test fixture_matrix`
