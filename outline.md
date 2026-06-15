# Runtime Transport Spine

This is the one story compiler2 should be telling from semantics down to native
codegen. There is one shape. Every layer reads it. No layer rebuilds it.

## The One Rule

A runtime value has exactly one transport shape. It is built once, and it is a
spine of stable ids. The facts that differ between layers do not live in the
spine — they live in tables those ids index. A layer changes which table it
reads; it never changes, copies, or translates the spine.

Once the shape is built, downstream does not reinterpret it, widen it, narrow
it, re-emit it, or recover it from a smaller summary. It indexes it.

## The Spine

```
Shape = Nothing | Scalar(ScalarId) | Tuple(Vec<ShapeId>) | Callable(CallableId)
```

- Built once, when demand settles. Thereafter it is referenced, never copied.
- `ShapeId` names a node in the settled root-scoped transport spine.
- `ScalarId` names a scalar leaf. When the leaf corresponds to an existing body
  value, it is rooted in `ValueId`; when it is an interior tuple leaf with no
  `ValueId`, the spine mints a small stable scalar id.
- `CallableId` names a callable identity. Locality, directness, capture lanes,
  first-class materialization, and boundary boxing are facts about that
  `CallableId`; they are not shape variants.
- Executable transport roots are keyed by the existing semantic identities:
  `FunctionId` -> `ActivationKey { function, input }` -> `ExecutableKey`.
- `Nothing` is the single "not transported" node. There is no `Ignore` here and
  no `Omitted` there and no third spelling somewhere else — one node, one
  meaning: this slot carries no runtime value.

## Required First Move

Before any transport-spine implementation work, rename the doomed vocabulary with
an explicit trash marker. The prefix should make the code uncomfortable to wire
back in:

```
RuntimeValueLayout -> TrashRuntimeValueLayout
RuntimeInputLayout -> TrashRuntimeInputLayout
RuntimeLane -> TrashRuntimeLane
DeliveredShape -> TrashDeliveredShape
NativeDemandAbi -> TrashNativeDemandAbi
```

Do the same for recursive value mirrors and shape-translation helpers where they
are transport authority. This is a guardrail commit, not the redesign: pure
rename, no behavior work, no aliases, no bridge layer. If a later change tries
to add a dependency on `Trash*`, the name itself should force the "why am I
wiring garbage back in?" moment.

## Facts Live in Tables, Keyed by the Spine's Ids

Everything that used to be a *variant payload* is a *table column* indexed by the
id the spine already holds:

- a `Scalar`'s representation lane — computed once from the node's type
  (`repr = abi_value_repr(ty)`), then stored as a fact and read, never recomputed
  per consumer
- a `Callable`'s captured surface, its flat capture lanes, its boundary boxing —
  columns keyed by `CallableId`
- the boundary's published lane contract — the same spine, a different column
- codegen's `ArgRepr` lanes — the same spine, another column

The layer selects the column. The id and the structure are invariant across all
of them.

## What Is Not In The Spine

Two facts deliberately ride *alongside* the shape, not inside it:

- **Divergence.** "Never returns" is `is_empty(return_ty)` — a per-executable
  bit. It is not a node. A diverging executable has a shape *and* a set bit; the
  bit is not a fourth spelling of `Nothing`.
- **The demand seed.** `ExecutableNeed` (`Value | TupleFields(arity)`) is the
  coarse key that *precedes* the spine: it identifies the executable we settle a
  shape *for*. It stays coarse on purpose — keying on the full shape mints a new
  specialization per distinct shape and the spec count explodes. The seed is the
  key; the spine is the result.
- **Runtime demand.** `RuntimeDemand` is the pre-spine lattice used to discover
  what must be transported. It is allowed to contain `Ignore`; the settled spine
  is not. `Ignore` becomes `Nothing` exactly once during spine construction.

## The Disease: Spine Translation

Any function that walks one shape and emits another shape is the disease. It
forces a second structure to be maintained by hand, and the moment the two fall
out of step you have a latent bug — a variant added to one spine and forgotten
in the other. That is exactly how a realized spine once lost its `Nothing` case
and crashed when a discarded capture flowed through it.

So these do not exist:

- deriving a per-node layout by walking a demand spine
- deriving a boundary ABI by walking a layout spine
- deriving a codegen delivery shape by walking a layout or ABI spine
- a realized value tree that mirrors the layout tree with different leaves
- deriving scalar or codegen reprs from types below the spine/fact-table seam

There is one spine. Downstream indexes it. If a layer holds its own copy of the
structure, authority has leaked into that layer.

## Removal Targets

These names may exist during migration, but they are not the destination:

- `RuntimeValueLayout`
- `RuntimeInputLayout`
- `RuntimeLane`
- `DeliveredShape`
- `NativeDemandAbi`
- recursive `RealizedValue` or `BackendValue` layout mirrors
- codegen-side `ArgRepr::from_ty` decisions for compiler2 transport lanes

The replacement for each is the same: read the settled spine, then index the
fact table for the lane or boundary fact needed at that seam.

## Boundaries

A true boundary — crossing a callable, publishing a first-class entry surface,
adapting at an extern — reads the *same* spine and indexes a boundary fact
column. A callable that boxes to a single ref lane at a boundary is a fact at
that id (one `ValueRef` lane), not a reshaped tree. The boundary is a column on
the one shape, not a second shape. Boundary facts answer "what does this id
expose when control crosses here?" — they are never the internal model for
returns, captures, or continuation payloads, because those read the spine
directly.

## Codegen

Codegen is boring. It walks the one spine; at each id it reads that node's
codegen lane fact; it writes those lanes and reads those lanes. It never decides
a shape, never re-derives a repr, never carries its own spine. Heap closures,
continuation closures, yielded continuations, resumed continuations, and direct
callable materialization are not distinct modeling problems — they are the same
operation: serialize a node's lanes per its settled fact, deserialize later by
the same fact.

## Correctness Standard

At every seam, ask one question:

Am I reading the one spine and indexing a fact table — or am I building, copying,
or translating structure?

If structure is being re-emitted anywhere below the point it was settled, the
model is wrong in that layer. One spine. Stable ids, rooted at `FunctionId`.
Facts in tables. Nothing re-walked, nothing re-spelled.
