# Runtime Transport Spine

This is the one story compiler2 should be telling from semantics down to native
codegen. There is one information-flow graph. Every layer reads it. No layer
rebuilds it.

## The One Rule

A runtime value has exactly one transport shape. It is built once into a
root-scoped `TransportPlan`, using shared interned descriptor ids. The facts
that differ between layers do not live in the shape descriptor — they live in
tables those ids index. A layer changes which table it reads; it never changes,
copies, or translates the shape.

Once the shape is built, downstream does not reinterpret it, widen it, narrow
it, re-emit it, or recover it from a smaller summary. It indexes it.

## The Spine

```
Shape = Nothing | Lane(LaneId) | Tuple(Vec<ShapeId>) | Callable(CallableId)
```

- Built once per settled transport position. Thereafter it is referenced, never
  copied.
- `ShapeId` names an interned shape descriptor. This mirrors the type interner:
  recursive children are ids, so interning goes all the way down. The descriptor
  interner can be shared across roots and runs when its key material is stable;
  root-scoped validity lives in `TransportPlan`, not in the descriptor id.
- `LaneId` names one non-callable transported leaf. Today that leaf is keyed by
  its settled `Ty`; if ownership introduces two different transport obligations
  for the same `Ty`, the descriptor becomes `{ ty, transport_class }`. It is
  still one leaf id, not a value id.
- `CallableId` names a callable identity. Its descriptor may contain any
  immutable key material that actually defines identity. Maximal sharing comes
  from keeping root-relative evidence out of the descriptor; locality, direct
  surfaces, and published boundary obligations are facts about that
  `CallableId`, not shape variants. Ordered capture lane payload is descriptor
  key material when it distinguishes callable identity; the same ordered payload
  is also exposed as a fact for consumers.
- `BoundaryId` names one published callable contract. A callable may have zero
  or more boundary contracts. Boundary publication is contextual and cannot be
  the identity of `CallableId` or `LaneId`.
- Executable transport symbols are pure semantic meaning:
  `FunctionId` -> activation symbol `{ function, input }` -> executable symbol
  `{ activation, need }`. `RootId` owns a closure/query over those symbols; it
  should not be part of shareable identity unless the thing truly changes
  meaning per root.
- `Nothing` is the single "not transported" node. There is no `Ignore` here and
  no `Omitted` there and no third spelling somewhere else — one node, one
  meaning: this slot carries no runtime value.
- `ValueId` is not shape identity. Body values, entry slots, return positions,
  captures, and continuation payloads map to `ShapeId` through separate facts.

## Source Data And Product

The source data is semantic evidence, not layout:

- semantic identities: `RootId`, `FunctionId`, `ActivationKey`,
  `ExecutableKey`, `ValueId`, callsite ids, and entry ids
- type evidence: interned `Ty`, per-value types, and settled return evidence
- demand evidence: `RuntimeDemand`, including `Ignore`, whole value,
  tuple-field demand, and callable demand with exact surfaces, escape, and
  opaque facts
- callable-flow evidence: per local callable producer target function, ordered
  captures, direct surfaces, first-class boundary surfaces, opaque/escape bits,
  and canonical executable resolutions when the callable is directly reached
- flow evidence: lowered control edges, call summaries, resume destinations,
  entry captures, and local callable producers
- boundary evidence: which callable values actually escape or publish a
  first-class surface

The product has two levels: shared descriptors plus one root-scoped transport
plan.

```
SemanticClosed(root) + settled RuntimeDemand
  -> shared descriptor interners
  -> TransportPlan(root)
  -> TransportPosition -> ShapeId
  -> LaneId facts
  -> CallableId facts
  -> BoundaryId facts
  -> codegen seam facts
```

The plan answers "what runtime structure moves at this seam?" exactly once.
Backends answer "how do I emit this seam?" by reading facts from the plan.

Implementation status after `fz-hwn.20.8.9`: `src/compiler2/transport.rs`
defines the root-independent ids, descriptors, transport symbols,
`TransportPosition`, `TransportInterners`, and `TransportStore`. `World` owns one
`TransportStore`. `DeriveTransportPlan(root)` now populates root-scoped
positions plus `CallableId` and `BoundaryId` fact tables from settled semantic
evidence. Boundary contracts preserve callable leaves as one published value
lane and preserve tuple returns as recursive boundary-return contracts, not flat
lane lists. Boundary returns are published per surface, so one callable used at
two surfaces has two contracts when those return transports differ. Local
callable projection now requires upstream `CallableFlowFact` evidence for the
producer, captures, direct surfaces, first-class surfaces, canonical
resolutions, and capture demands; missing evidence is an invariant failure, not
a transport-side type fallback. Generic opaque callable descriptors project
surfaces carried by upstream `RuntimeDemand::Callable`; transport no longer
recovers missing callable surfaces from type. Recursive resume positions read
the upstream value demand for the delivered resume value instead of recomputing
that demand from callsite summaries. Capture lane facts preserve payload order
and duplicate lanes. Direct-call surfaces and first-class boundary publication
are independent facts, so one callable can have both. Generic callable
descriptors include stable contract-surface key material, so opaque callable
contracts with different observed surfaces cannot merge into one `CallableId`.
Recursive callsite return sources are treated as recursive shape constraints,
not as a reason to fall back to generic callable shape when non-recursive
sources prove the identity.
Boundary publication facts only name real semantic positions; there is no
synthetic boundary self-position. `DeriveTransportPlan(root)` is scheduled as a
side-output of settled semantic closure and is also re-requested if the
root-scoped plan is missing. Materialization now waits on `TransportPlan(root)`
and carries plan-backed positions, callable ids, boundary ids, and seam facts
through the artifact/backend handoff. Native handoff metadata reads seam facts
for executable returns, callable boundary returns, delivered continuation
payloads, and entry captures; it does not recover those ABI reprs from lane
types. Codegen seam facts are now plan-owned facts for the worked scalar,
tuple-leaf, and boxed-lane seams. Function entry, return delivery, tail call,
and extern boundary use raw lane reprs when settled type evidence proves
`RawInt`, `RawF64`, or `RawAtom`; otherwise they publish `ValueRef`. Block
parameter and continuation entry use `ValueRef` for float and boxed leaves and
raw integer/atom reprs for integer/atom leaves. Callable boundary and
first-class publication lanes use `ValueRef`. Executable input
positions are solved from shape anchors plus equality edges, not from repeated
map overwrites. Shape anchors say one semantic position has one concrete
`ShapeId`; equality edges say two `TransportPosition`s must share one `ShapeId`.
Solving unions the positions, then each connected component must have
zero or one distinct anchored `ShapeId`. Because shapes are interned all the way
down, conflict detection is literal `ShapeId` inequality. Producer value, call
argument, executable input, callable capture-prefix input, and clause parameter
value positions therefore converge on one `ShapeId` by construction. There is no
separate capture/input shape cache and no pass-order-dependent propagation loop.
Callable-shaped seams publish their descriptor-owned capture lanes as codegen
seam facts. These facts are derived from `TransportPlan` positions and boundary
contracts only. The transport calculator reads `RuntimeDemand` plus semantic
`callable_flows`, not the old callable-materialization inventory, and no old
`Trash*` layout is translated into descriptors.

## Required First Move

Before any transport-spine or parallel-flow implementation work, rename the
doomed vocabulary with an explicit trash marker. The prefix should make the code
uncomfortable to wire back in:

```
RuntimeValueLayout -> TrashRuntimeValueLayout
RuntimeInputLayout -> TrashRuntimeInputLayout
RuntimeParamLayout -> TrashRuntimeParamLayout
RuntimeLane -> TrashRuntimeLane
ReturnAbi -> TrashReturnAbi
DeliveredShape -> TrashDeliveredShape
NativeDemandAbi -> TrashNativeDemandAbi
RealizedValue -> TrashRealizedValue
BackendValue -> TrashBackendValue
```

Do the same for recursive value mirrors and shape-translation helpers where they
are transport authority. This is a guardrail commit, not the redesign: pure
rename, no behavior work, no aliases, no bridge layer, and no `ShapeId` /
`BoundaryId` / `TransportPlan` implementation. If a later change tries to add a
dependency on `Trash*`, the name itself should force the "why am I wiring garbage
back in?" moment.

## Construction Strategy

Use the **Output Contract Loop** with parallel construction and independent
authority.

1. Work the output contract on paper and pin it with telemetry/tests.
2. Build the clean `TransportPlan` beside the old path from the same semantic
   evidence and settled demand.
3. Let the old path continue to carry current behavior while the new model is
   proven.
4. Never translate old layout into new shape, or new shape back into old layout.
   The old path is a behavior oracle and removal inventory only.
5. Once the independent plan is proven, cut consumers over seam by seam and
   delete the trash-prefixed old authority at each seam.

This is not a strangler adapter. The new fact store is independently derived
from `SemanticClosed(root)`, `RuntimeDemand`, type evidence, lowered flow, and
callsite/callable evidence. The cutover consumes that store; it does not ask the
old layout code what the new facts mean.

## Facts Live in Tables, Keyed by Transport Ids

Everything that used to be a *variant payload* is a *table column* indexed by the
id the descriptor graph or `TransportPlan` already holds:

- a `Lane`'s settled type and stable transport class — computed once from the
  settled type/fact evidence, then stored as facts and read, never recomputed per
  consumer
- a `Callable`'s direct surfaces and published boundary ids — root-scoped
  columns keyed by `CallableId`
- a `Callable`'s ordered flat capture lanes — descriptor-owned identity payload
  keyed by `CallableId`, because one callable identity cannot have two payload
  lane sequences
- a boundary's published lane contract — columns keyed by `BoundaryId`
- codegen lane representations — columns keyed by the lane plus the codegen seam
  that consumes it

The layer selects the column. The id and the structure are invariant across all
of them.

## What Is Not In The Spine

Some facts deliberately ride *alongside* the shape, not inside it:

- **Divergence.** "Never returns" is `is_empty(return_ty)` — a per-executable
  bit. It is not a node. A diverging executable has a shape *and* a set bit; the
  bit is not a fourth spelling of `Nothing`.
- **The demand seed.** `ExecutableNeed` (`Value | TupleFields(arity)`) is the
  coarse key that *precedes* the plan: it identifies the executable we settle a
  shape *for*. It stays coarse on purpose — keying on the full shape mints a new
  specialization per distinct shape and the spec count explodes. The seed is the
  key; the plan is the result.
- **Root ownership.** `RootId` owns a closure/query over symbols and facts. It
  is not automatically part of activation, executable, shape, lane, callable, or
  boundary descriptor identity.
- **Semantic value identity.** `ValueId` identifies semantic values. It maps to
  `ShapeId`; it is not embedded in `Shape`, `LaneId`, or `CallableId` unless the
  value itself is deliberately part of some descriptor's identity. That should
  be rare because it narrows sharing.
- **Runtime demand.** `RuntimeDemand` is the pre-spine lattice used to discover
  what must be transported. It is allowed to contain `Ignore`; the settled spine
  is not. `Ignore` becomes `Nothing` exactly once during spine construction.
- **Boundary publication.** A boundary contract is keyed by `BoundaryId` and
  points at the same shape ids. It is not a shape variant.
- **Codegen representation.** `ArgRepr`-like facts are seam-specific. For
  example, a float may travel as `RawF64` through a function ABI but must be a
  `ValueRef` across a block-param seam, while integer and atom lanes can remain
  raw across that seam. That is a codegen fact, not `Shape`.

## The Disease: Spine Translation

Any function that walks one shape and emits another shape is the disease. It
forces a second structure to be maintained by hand, and the moment the two fall
out of step you have a latent bug — a variant added to one spine and forgotten
in the other. That is exactly how a realized spine once lost its `Nothing` case
and crashed when a discarded capture flowed through it.

So these do not exist:

- deriving a per-node layout by walking a demand spine
- deriving a published boundary contract by walking a layout spine
- deriving a codegen delivery shape by walking a layout or boundary-contract spine
- a realized value tree that mirrors the layout tree with different leaves
- deriving lane or codegen reprs from types below the plan/fact-table seam

There is one descriptor graph and one root plan that indexes it. Downstream
indexes the plan. If a layer holds its own copy of the structure, authority has
leaked into that layer.

## Removal Targets

These names may exist during migration with a `Trash` prefix, but they are not
the destination:

- `RuntimeValueLayout`
- `RuntimeInputLayout`
- `RuntimeParamLayout`
- `RuntimeLane` (the old layout leaf, not the new `LaneId`)
- `ReturnAbi`
- `DeliveredShape`
- `NativeDemandAbi`
- recursive `RealizedValue` or `BackendValue` layout mirrors
- codegen-side `ArgRepr::from_ty` decisions for compiler2 transport lanes

The replacement for each is the same: read `TransportPlan`, then index the fact
table for the lane, callable, codegen seam, or published boundary contract
needed at that seam.

### `fz-hwn.20.6` Handoff Inventory

This inventory is backed by:

```
rg -n "\b(TrashRuntimeValueLayout|TrashRuntimeInputLayout|TrashRuntimeParamLayout|TrashRuntimeLane|TrashReturnAbi|TrashDeliveredShape|TrashNativeDemandAbi|TrashRealizedValue|TrashBackendValue|LocalCallableId|runtime_value_layout_from_demand|runtime_input_layout_from_demand|trash_delivered_shape_from_layout|trash_delivered_shape_from_return_abi|tuple_return_delivery_plan|local_callable_layout|boundary_return_abi|ArgRepr::from_ty|for_block_param_ty)\b" src/compiler2 src/ir_interp src/ir_codegen
```

Cutover classification:

- `src/compiler2/artifact.rs`, `src/compiler2/jobs/artifact.rs`,
  `src/compiler2/jobs/backend.rs`, and `src/compiler2/world.rs` no longer carry
  `TrashRuntimeValueLayout`, `TrashRuntimeInputLayout`,
  `TrashRuntimeParamLayout`, `TrashRuntimeLane`, `TrashReturnAbi`,
  `LocalCallableId`, local-callable layout memoization, `local_callable_layout`,
  or `boundary_return_abi` as live artifact authority. The focused
  transport/artifact seam now uses `TransportPosition -> ShapeId`, executable
  membership, `CallableId` facts, `BoundaryId` contracts, and seam facts from
  `TransportPlan`.
- `src/ir_interp/backend.rs`, `src/ir_interp/mod.rs`, and
  `src/compiler2/jobs/native.rs` still carry recursive runtime-value mirrors:
  `TrashBackendValue` and `TrashRealizedValue`. `fz-hwn.19.4` replaces those
  mirrors with `ShapeId` or `TransportPosition` plus lane bundles/spans; tuple
  fields are child shape views and direct callables carry `CallableId`.
- `src/compiler2/native_codegen/demand.rs`,
  `src/compiler2/native_codegen/driver.rs`,
  `src/compiler2/native_codegen/entry.rs`,
  `src/compiler2/native_codegen/function.rs`,
  `src/compiler2/native_codegen/terminator.rs`, and
  `src/compiler2/native_codegen/prim.rs` still carry `TrashDeliveredShape`,
  `TrashNativeDemandAbi`, `trash_delivered_shape_from_layout`,
  `trash_delivered_shape_from_return_abi`, continuation-shape recovery, and
  compiler2-local `ArgRepr` decisions. `fz-hwn.19.5` replaces those with
  `CodegenSeamFact` reads keyed by `LaneId` plus `CodegenSeam`; low-level
  `ArgRepr` may remain only as an emission enum filled from those facts.
- `src/ir_codegen/*` still has non-compiler2 legacy `ArgRepr::from_ty` and
  `for_block_param_ty` paths. They are not inputs to the new transport plan.
  They are either outside the compiler2 cutover or must be named by a separate
  legacy-codegen ticket before `fz-hwn.19.6` deletes the remaining old
  vocabulary.

### `fz-hwn.19.2` Transport/Artifact Seam Epic

Goal: make the artifact ladder consume `TransportPlan(root)` as settled input.
Artifact may package closed bodies, call edges, effects, extern marshals, stable
inventory ids, and backend/native handoff records. It must not calculate how
values move.

Seam input:

```
SemanticClosed(root) + TransportPlan(root)
  -> MaterializedProgram(root)
  -> AbiReadyProgram(root)
  -> EmissionReadyProgram(root)
  -> BackendProgram(root)
```

Transport owns `TransportPosition -> ShapeId`, `ShapeId` structure, lane facts,
`CallableId` facts, `BoundaryId` contracts, and `CodegenSeamFact` rows. Artifact
owns only stable projection and indexing over those facts. If artifact needs to
know a runtime lane, callable target, boundary publication, resume payload, or
codegen representation, it reads the plan/fact table. It does not walk
`RuntimeDemand`, `TrashRuntimeValueLayout`, local types, or lowered bodies to
re-derive the answer.

Child ticket order:

1. `fz-hwn.19.2.1` pins artifact-facing worked source tests. Producer return and
   delivered resume share one `ShapeId`; direct callable return/resume reads
   `CallableDescr` identity payload plus `CallableFacts` direct-call usage;
   escaped callable publication reads `BoundaryId`; ignored local use cannot
   mutate the received transport shape.
2. `fz-hwn.19.2.2` changes `MaterializedProgram` to carry plan revision plus
   transport refs/facts, then deletes `MaterializeRoot`'s
   `derive_runtime_transports` writeback for inputs, returns, resumes, and entry
   captures.
3. `fz-hwn.19.2.3` makes ABI-ready and callable-entry inventory read seam facts,
   `CallableId`, and `BoundaryId` facts, then deletes local callable witness
   layout derivation and `trash_boundary_return_abi`.
4. `fz-hwn.19.2.4` carries the transport-backed artifact handoff through
   emission/backend records without `TrashRuntime*` or `TrashReturnAbi` fields.
   The current WIP has banked the first removal slice; remaining `.4` work is
   one output-contract ticket per disabled downstream test:
   `fz-hwn.19.2.4.1` re-enables
   `compiler2_interp_runs_spawned_children_from_backend_runtime_intrinsics`;
   `fz-hwn.19.2.4.2` re-enables
   `compiler2_interp_runs_spawn_opt_children_from_backend_runtime_intrinsics`;
   `fz-hwn.19.2.4.3` re-enables
   `compiler2_native_multi_relay_delivers_resume_values_through_continuation_abi`;
   `fz-hwn.19.2.4.4` re-enables
   `compiler2_interp_runs_resource_dtors_from_backend_runtime_intrinsics`;
   `fz-hwn.19.2.4.5` re-enables
   `compiler2_native_program_resource_fixture_shapes_callable_boundaries_explicitly`;
   `fz-hwn.19.2.4.6` re-enables
   `compiler2_run_root_jit_executes_resources_without_legacy_prepare`.
   Each ticket starts by turning on its test, then fixes only the proven
   transport/artifact seam violation. No downstream recomputation, fallback
   layout derivation, compatibility adapter, or copied interner table is allowed.
5. `fz-hwn.19.2.5` removes leftover artifact authority, updates docs/telemetry,
   and proves with `rg` that live artifact/materialization code no longer
   imports or constructs the trash-prefixed transport model.

This epic gates `fz-hwn.19.3` through `fz-hwn.19.5`. Those downstream tickets
are not allowed to rediscover artifact facts; they consume the transport-backed
artifact inventory produced here.

## Boundaries

A true boundary — crossing a callable, publishing a first-class entry surface,
adapting at an extern — reads the *same* plan and indexes a published boundary
contract column. A callable that boxes to a single ref lane at a boundary is a
fact at that id (one `ValueRef` lane), not a reshaped tree. The boundary
contract is a column on the one shape, not a second shape. Boundary facts answer
"what does this id expose when control crosses here?" — they are never the
internal model for returns, captures, or continuation payloads, because those
read `TransportPlan` directly.

A `CallableId` may have multiple `BoundaryId`s. They share callable identity but
publish different contracts when grounded surfaces, capture types, argument
lanes, or return contracts differ.

## Codegen

Codegen is boring. It walks the one descriptor graph through `TransportPlan`; at
each id it reads that node's codegen facts for the seam being emitted; it writes
those lanes and reads those lanes. It never decides a shape, never re-derives a
repr, never carries its own spine. Heap closures, continuation closures, yielded
continuations, resumed continuations, and direct callable materialization are
not distinct modeling problems — they are the same operation: serialize a node's
lanes per its settled fact, deserialize later by the same fact.

## Worked Example

Consider this root:

```
make_adder(n):
  return fn add(x): n + x

pair(n):
  return { n, make_adder(n) }

main():
  { n, add } = pair(41)
  y = add(1)

  pub = make_adder(10)
  escape_as_callable(pub, surface: (int) -> int)

  return y
```

Assume every number has type `int`.

The semantic and demand facts are:

```
E_pair = ExecutableKey(pair/1, need = TupleFields(2))
E_add  = ExecutableKey(add/2, need = Value)      # capture n, arg x
E_main = ExecutableKey(main/0, need = Value)

RuntimeDemand(E_pair.return) = TupleFields([Value, Callable(resolved [int])])
RuntimeDemand(E_add.return) = Value
RuntimeDemand(pub) = Callable(resolved [int], escape = true)
```

The descriptor interners contain:

```
L_int = LaneId { ty = int }
S_int = Shape::Lane(L_int)

C_direct = CallableId {
  target = E_add,
  capture_shapes = [S_int],
  capture_lanes = [L_int],
}
C_direct facts = {
  direct_surfaces = [[S_int]],
  boundary_ids = [],
}
S_direct_callable = Shape::Callable(C_direct)

S_pair_return = Shape::Tuple([S_int, S_direct_callable])

C_pub = CallableId {
  target = E_add,
  capture_shapes = [S_int],
  capture_lanes = [L_int],
}
C_pub facts = {
  direct_surfaces = [],
  boundary_ids = [B_pub],
}
S_pub_callable = Shape::Callable(C_pub)

B_pub = BoundaryId {
  callable = C_pub,
  surface_arg_shapes = [S_int],
  published_value_lane = L_callable_ref,
  published_capture_lanes = [L_int],
  published_arg_lanes = [L_int],
  published_return_shape = S_int,
  published_return_lanes = [L_int],
}
```

The root plan maps semantic seams to descriptor ids:

```
Pos(E_pair.input[0])          -> S_int
Pos(E_pair.return)            -> S_pair_return
Pos(E_main.resume(pair call)) -> S_pair_return
Pos(E_add.input[0])           -> S_int      # captured n
Pos(E_add.input[1])           -> S_int      # x
Pos(E_add.return)             -> S_int
Pos(E_main.value(pub))        -> S_pub_callable
```

`pair(41)` returns `S_pair_return`. The first child contributes one `L_int`
lane. The second child is `Shape::Callable(C_direct)`, whose descriptor-owned
capture lanes say it contributes one captured `L_int` lane. The physical return
lanes are:

```
[ L_int(n), L_int(captured n) ]
```

No tuple object is required. No closure object is required. The tuple shape
names the two fields; the callable descriptor names the target and capture
lanes, while callable facts name direct surfaces and boundary publications.

`main` receives the result through the same `S_pair_return`:

```
field 0 -> S_int -> n = 41
field 1 -> Shape::Callable(C_direct) -> add = { callable: C_direct, captures: [41] }
```

Producer and consumer cannot disagree because the root plan maps return and
resume to the same `ShapeId`. There is no return layout and resume layout to
keep compatible.

The direct call `add(1)` reads `C_direct`:

```
C_direct.target = E_add
C_direct.capture_shapes = [S_int]
call arg shape = S_int

E_add physical input lanes = [ captured n, arg x ] = [ 41, 1 ]
E_add return shape = S_int
```

The escaped callable `pub` uses the same callable shape class but a boundary
contract:

```
Pos(E_main.value(pub)) -> S_pub_callable
S_pub_callable = Shape::Callable(C_pub)
C_pub.boundary_ids = [B_pub]
```

Publishing reads `B_pub`, which says how to materialize the first-class callable
and what lanes its public call surface accepts and returns. Internally the value
is still `Shape::Callable(C_pub)`. The boundary is a published contract, not a
new internal shape.

This example covers the required cases:

```
Ignore           -> Shape::Nothing
Value int        -> Shape::Lane(L_int)
Tuple fields     -> Shape::Tuple([...])
Direct callable  -> Shape::Callable(C_direct) + descriptor capture lanes + callable facts
Escaped callable -> Shape::Callable(C_pub) + BoundaryId contract
Resume payload   -> same ShapeId as producing return
Codegen repr     -> seam fact, not shape
```

## Output Contract Signal

The contract test for this model lives in
`src/compiler2/transport_contract_test.rs`. `fz-hwn.20.3` turns the
production-boundary test on against the real `TransportPlan(root)` job/fact and
adds targeted fixtures for ignored returns, tuple return/resume sharing, and
direct-callable return/resume sharing. `fz-hwn.20.4` adds worked source
fixtures for callable/boundary facts: unused callable constructors publish no
boundary, direct lambda calls stay direct-only, escaped lambdas publish exactly
one first-class boundary, opaque callable inputs publish an explicit boundary,
same-surface callables remain distinct when their capture obligations differ,
boundary tuple returns preserve recursive structure, duplicate same-typed
captures remain duplicate ordered payload lanes, multi-surface callable
boundaries publish return contracts per surface, directly recursive tuple
returns share return/resume shapes, and callables captured for direct use are
not upgraded into first-class boundaries. The gap-closing `.4` fixtures also pin
that opaque callable contracts with different observed surfaces do not share one
`CallableId`, recursive callable returns preserve the resolved local callable
identity, missing side-product plans are regenerated even when the semantic
closure itself is unchanged, and boundary publications never use a synthetic
self-position. `fz-hwn.20.5` adds worked scalar and tuple-leaf fixtures for
function-entry vs block-param representation splitting, return delivery,
continuation entry, tail-call delivery, callable boundary publication, extern
boundary delivery, and per-kind seam telemetry counts. `fz-hwn.20.6` adds
boxed-lane fixtures pinning that non-raw transported leaves publish explicit
`ValueRef` seam facts instead of disappearing from the codegen fact table.

`fz-rh2.26` resolved the `fz-hwn.20.7.blocker` semantic/fixpoint break that
blocked callable boundary contracts. The worked source is a suspend-shaped
boundary return:

```fz
fn make_suspender() do
  fn (acc) ->
    {:suspended, acc, fn () -> {:cont, acc + 1} end}
  end
end

fn main(), do: make_suspender()
```

The transport contract is an escaped callable whose published return shape is
`Tuple([tag lane, acc lane, callable resume child])`, with boundary lane facts
flattening those three leaves without replacing the recursive return shape. The
failure was before transport construction: `SealSemanticClosure(root)`
discovered runtime-demand latent executables for the outer suspend lambda, the
captured resume lambda, and `Kernel.+/2 [α0, int]`, then later treated one of
its own dirty latent `Activation` facts as unavailable, completed a partial
wait-free pass, and retracted the resume lambda's `ActivationInputs`.

The fix is the semantic authority rule: activations published by
`SealSemanticClosure` in the current pass are known by construction for that
pass, while activation facts from other publishers still use the settled gate.
That removes the self-dependency without making stale frontier facts permanent;
normal rebased wait-free conclusions still retract frontiers after real source
changes. The source fixture is now a live contract test and must not be weakened
to a non-capturing resume function.

The landed derivation boundary is explicit: callable and boundary facts are
derived by the new transport calculator from settled demand, lowered callable
use sites, local callable producers, captures, callsite summaries, and settled
type evidence. The old layout and native boundary inventories are not inputs to
the transport plan. The old callable-materialization store has been deleted;
semantic `callable_flows` are the single callable obligation source.
Call-boundary argument demand is settled upstream: when a direct or closure call
argument falls back to whole-value demand, callable-typed values are upgraded by
the same boundary rule used for returns and matcher boundaries. Transport does
not recover that escape from type. Callable resolutions in `TransportPlan` are
also gated through `world.activation_key(...)` and the settled semantic
executable contexts, so a plan cannot publish a callable target that is outside
the root's executable membership.
After `fz-hwn.20.8.3`, `ExecutableRuntimeDemand` carries `callable_flows`:
upstream facts keyed by local callable producer `ValueId`. Each flow names the
producer target, ordered captures, direct surfaces, first-class publication
surfaces, opaque/escape bits, and canonical executable resolutions. Direct
surfaces are linked from locally called executable membership. First-class
surfaces come from settled callable demand, or from the producer's settled type
when a callable escapes without an observed call surface. This keeps "body
exists for first-class publication" distinct from "body is directly invoked at
this surface" before transport runs.
After `fz-hwn.20.8.9`, the local callable handoff is strict. Boundary
return demand, callable capture demand, boundary return resolutions, resume
payload demand, and generic callable surfaces are proven upstream. Transport
projects those facts into descriptors and plan positions; if a local callable
flow cannot name the required surface, resolution, or root context, that is an
invariant failure rather than a request for transport to recover the missing
information from type or callsite shape.

Test builds install a `World`-level `TransportPlanTestHandler` that receives
`&World` and the committed `RootId` after each plan definition. The default
handler validates the reachable plan graph vertically from the final
`TransportPlan(root)` roots without serializing extra telemetry or treating
unreachable interned work-product as an error.

Plan construction emits exactly one output signal:

```
fz.compiler2.transport_flow.defined
```

Measurements:

```
root_id
semantic_revision
executable_count
transport_position_count
shape_descriptor_count
lane_descriptor_count
callable_descriptor_count
boundary_descriptor_count
nothing_shape_count
tuple_shape_count
callable_shape_count
direct_callable_count
first_class_callable_count
boundary_publication_count
codegen_seam_fact_count
codegen_function_entry_seam_fact_count
codegen_block_param_seam_fact_count
codegen_return_delivery_seam_fact_count
codegen_continuation_entry_seam_fact_count
codegen_tail_call_seam_fact_count
codegen_callable_boundary_seam_fact_count
codegen_extern_boundary_seam_fact_count
codegen_first_class_publication_seam_fact_count
```

Metadata:

```
entry_executable_symbol
executable_membership
transport_positions
shape_descriptors
lane_descriptors
callable_facts
boundary_facts
seam_facts
```

The event is emitted by clean transport-flow derivation, not by old
materialization. Descriptor metadata must not contain root-relative evidence
such as `RootId`, `ValueId`, callsites, or resume points. Root-scoped evidence
belongs in `TransportPlan` metadata: membership, positions, demand/use
obligations, boundary publication, and seam facts. The event must not serialize
`Trash*` layout facts or `ArgRepr`-from-type decisions as authority. After
`fz-hwn.20.6`, `codegen_seam_fact_count` and per-kind seam counts report the
plan-owned seam facts for raw and boxed leaves; `seam_facts` is non-empty only
when a worked source-level example requires the fact.

The minimality check is mechanical:

- without `Nothing`, ignored slots need a fake payload
- without `Lane`, scalar runtime data has no leaf
- without `Tuple`, tuple-field transport collapses to boxed values
- without `Callable`, direct callables become heap closures or anonymous lane
  tuples with no target identity
- without `BoundaryId`, one callable identity cannot publish multiple contracts
- with `ValueId` inside `Shape`, equal structures stop interning
- with boundary or codegen repr inside `LaneId`, seam choices fork the shape

## Correctness Standard

At every seam, ask one question:

Am I reading `TransportPlan` and indexing a fact table — or am I building,
copying, or translating structure?

If structure is being re-emitted anywhere below the point it was settled, the
model is wrong in that layer. Shared descriptor ids. Root-scoped plans. Facts in
tables. Nothing re-walked, nothing re-spelled.
