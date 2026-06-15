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
  from keeping root-relative evidence out of the descriptor; locality,
  directness, capture lanes, first-class materialization, and published boundary
  obligations are facts about that `CallableId`, not shape variants.
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

Implementation status after `fz-hwn.20.2`: `src/compiler2/transport.rs`
defines the root-independent ids, descriptors, transport symbols,
`TransportPosition`, `TransportInterners`, and `TransportStore`. `World` owns one
`TransportStore`. No materialization, backend, native, or codegen consumer reads
these ids yet, and no old `Trash*` layout is translated into descriptors.

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
- a `Callable`'s captured surface, flat capture lanes, first-class
  materialization, and published boundary ids — columns keyed by `CallableId`
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
  `ValueRef` across a block-param seam. That is a codegen fact, not `Shape`.

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
  direct_surfaces = [[S_int]],
  boundary_ids = [],
}
S_direct_callable = Shape::Callable(C_direct)

S_pair_return = Shape::Tuple([S_int, S_direct_callable])

C_pub = CallableId {
  target = E_add,
  capture_shapes = [S_int],
  direct_surfaces = [],
  boundary_ids = [B_pub],
}
S_pub_callable = Shape::Callable(C_pub)

B_pub = BoundaryId {
  callable = C_pub,
  surface_arg_shapes = [S_int],
  published_capture_lanes = [L_int],
  published_arg_lanes = [L_int],
  published_return = Value(L_int),
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
lane. The second child is `Shape::Callable(C_direct)`, whose capture facts say
it contributes one captured `L_int` lane. The physical return lanes are:

```
[ L_int(n), L_int(captured n) ]
```

No tuple object is required. No closure object is required. The tuple shape
names the two fields; the callable fact names the target and capture lanes.

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
Direct callable  -> Shape::Callable(C_direct) + callable facts
Escaped callable -> Shape::Callable(C_pub) + BoundaryId contract
Resume payload   -> same ShapeId as producing return
Codegen repr     -> seam fact, not shape
```

## Output Contract Signal

The contract test for this model lives in
`src/compiler2/transport_contract_test.rs`. `fz-hwn.20.3` turns the
production-boundary test on against the real `TransportPlan(root)` job/fact and
adds targeted fixtures for ignored returns, tuple return/resume sharing, and
direct-callable return/resume sharing.

The landed derivation boundary is explicit: exact callable shapes are produced
only when semantic evidence names one local producer (`FunctionRef` or
`Lambda`) or one local callee return shape. Arbitrary joined callable inputs
stay generic value lanes until the later callable/boundary fact work lands.

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
`Trash*` layout facts or `ArgRepr`-from-type decisions as authority.

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
