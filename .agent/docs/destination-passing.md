# Destination Planning

Destination planning answers one question: where may a value be built before it
is published as ordinary immutable data? The compiler knows where a value is
going before it builds the value, so a tuple/list/map literal can construct
directly into its target storage and freeze once, without changing language
semantics.

The pieces that matter:

- **destination primitives in `fz_ir::Prim`** — explicit IR for building a
  tuple, list, or map through a linear init-token chain.
- **`ir_dest`** — lowers ordinary `MakeTuple`/`MakeList`/`MakeMap`/`MapUpdate`
  into those primitives, and verifies token/destination coherence.
- **planner typing** (`ir_planner::type_fn`) — folds the primitives with erased
  token facts to publish a precise value type at each freeze.
- **codegen** — lowers the verified primitives mechanically (typed struct
  setters, list-cons BIFs, map-dest helpers), with a static-struct fast path.

A **destination** is an unpublished construction location. An **init token** is
the erased linear IR identity that proves which write/freeze may happen next.
Once a destination is frozen, the result is ordinary immutable data; no later
primitive may mutate it.

Ownership of proof is the simplifying rule: IR carries construction intent, the
planner types it through token facts, the verifier checks token coherence, and
codegen lowers the facts. Backend shape recognition is never the proof.

Two adjacent mechanisms are not destination planning and own different state:

- **return delivery** (`ir_planner::fn_types::ReturnContract`) describes how a
  call edge returns; it creates no construction storage. See
  [`dispatch-as-planner-output.md`](dispatch-as-planner-output.md).
- **physical capabilities** such as owned-cons reuse are object-local
  permissions on private runtime objects, carried separately from semantic
  values.

[`single-authoritative-plan.md`](single-authoritative-plan.md) covers the
one-plan pipeline rule that destination lowering plugs into.

## IR Vocabulary

`fz_ir::Prim` owns the destination operations. Each `Stmt::Let` binds either a
destination handle, a dead unit marker, a fresh cons, or the published value.

- `DestTupleBegin { token, arity }` allocates an unpublished tuple destination
  and defines the first token.
- `DestTupleSet { dest, token, index, value, next }` consumes one token, writes
  one tuple field, and defines the next token.
- `DestFreeze { dest, token }` consumes the final tuple token and publishes the
  tuple value.
- `DestListBegin { token }` defines the first token for a destination-built
  list chain.
- `DestListCons { token, head, tail, next }` consumes one token, constructs one
  cons cell from `head` and a known `tail` (`tail: None` is the empty-list
  sentinel), and defines the next token.
- `DestListFreeze { list, token }` consumes the final list token and publishes
  the built list.
- `DestMapBegin { token, base, extra }` allocates an unpublished map
  destination; `base` seeds it from an existing map, `extra` is the entry count.
- `DestMapPut { map, token, key, value, next }` consumes one token, sets one
  key/value pair, and defines the next token.
- `DestMapFreeze { map, token }` consumes the final map token, canonicalizes
  ordering and deduplicates keys, and publishes the immutable map.

## Lowering

`ir_dest::lower_destinations` runs all three rewrites. Each rewrites a surviving
construction prim into a begin / set-or-cons / freeze chain over fresh vars and
fresh tokens.

`lower_tuple_destinations` rewrites each `MakeTuple`:

```text
dest = DestTupleBegin(tok0, arity=N)
_    = DestTupleSet(dest, tok0, index=0, value=v0, next=tok1)
...
out  = DestFreeze(dest, tokN)
```

`lower_list_destinations` rewrites each non-empty `MakeList` from right to left,
so each cons sees its already-built tail; empty-list literals stay the
empty-list sentinel:

```text
_  = DestListBegin(tok0)
c1 = DestListCons(tok0, head=b, tail=tail, next=tok1)
c0 = DestListCons(tok1, head=a, tail=c1, next=tok2)
xs = DestListFreeze(c0, tok2)
```

`lower_map_destinations` rewrites each `MakeMap` and `MapUpdate` (the update's
`base` becomes `DestMapBegin`'s `base`):

```text
m0  = DestMapBegin(tok0, base=base_or_none, extra=N)
_   = DestMapPut(m0, tok0, key=k0, value=v0, next=tok1)
...
out = DestMapFreeze(m0, tokN)
```

Lowering runs inside the codegen driver, after the planner has selected the
executable body, so init-token ownership stays local to the lowered body handed
to codegen. The driver re-runs the planner's type resolution and
`materialize_program` on the already-lowered module.

## Verification

`ir_dest::verify_module` owns structural correctness over the lowered IR and
runs in the codegen driver right after lowering.

Token coherence is checked for tuple, list, and map chains alike:

- token definitions are unique;
- each token is consumed at most once;
- a token is consumed only after it is defined.

Tuple destinations carry additional shape checks:

- fields are in bounds and written at most once;
- freeze requires every field to be initialized;
- a frozen destination is not written again;
- every begun destination is eventually frozen.

The tuple-state transitions (`define_init_token`, `consume_init_token`,
`begin_tuple_dest`, `set_tuple_dest_field`, `freeze_tuple_dest`) live in
`src/ir_dest/mod.rs` and are generic over a field payload. The verifier
instantiates them with `()`; the planner instantiates the same helpers with `Ty`
payloads, so verifier and typer cannot drift on what a legal chain looks like.

## Typing

`ir_planner::type_fn` types a function through a fixpoint; the per-statement
helper `type_let_with_init_facts` folds destination primitives with erased token
facts and falls back to `type_prim` for everything else. The token facts (init
tokens, tuple-dest states, per-token list and map value types) are local to that
fold — they are not stored in `SpecPlan`, because downstream consumers need only
the final value type of ordinary vars.

What each freeze publishes:

- **Tuple.** The tuple-dest state accumulates each field's `Ty`. `DestFreeze`
  publishes `tuple(fields)` from the complete state, not from the opaque
  destination handle type.
- **List.** A per-token fact carries the current list value type. `DestListCons`
  unions the head type with the tail's element type and binds the cons var to a
  precise non-empty list type; `DestListFreeze` publishes the token fact, with a
  fall back to the handle's type for malformed IR.
- **Map.** A per-token fact carries the current map value type. `DestMapBegin`
  seeds it from `base` or `map(&[])`. `DestMapPut` refines a static key with
  `var_as_map_key` + `refine_map_field`; a dynamic key widens to `map_top()`.
  `DestMapFreeze` publishes the token fact.

Malformed destination IR does not panic the planner: each fold checks its token
transitions and falls back conservatively, leaving diagnostics to the verifier.
Verified codegen never sees malformed IR. `type_prim` also has conservative
destination arms (handle/element lookups) used when destinations are typed
without the token-fact context.

## Return Delivery Boundary

`SpecKey` is `{ fn_id, input, demand }`. The semantic body identity is
`BodyKey` (`fn_id` + `input`); `demand` (a `ReturnDemand`) selects the return
ABI, not a different value payload. Demand is part of the spec identity, so the
same `BodyKey` reached with two different demands — a `tuple_fields` reach and a
`value` reach of one helper — materializes as two distinct native bodies, like
two type specializations. `materialize_program` lowers one body per spec and
does not merge demand siblings, because merging would force one return ABI onto
callers that asked for the other.

The executable call-edge fact is `ReturnContract { target: SpecKey, strategy:
ReturnStrategy }`. The strategies are:

- `Value` — ordinary material return;
- `TupleFields(N)` — the producer returns the `N` fields of an `N`-tuple in
  registers, skipping the struct box;
- `ForwardedDemand(demand)` — a tail-call edge forwards the caller's demand.

`ReturnDemand` itself carries `delivery: ReturnDelivery`, and `ReturnDelivery`
has exactly two shapes: `Value` and `TupleFields(usize)`. There is no list-tail
delivery shape. Recursive list construction needs none: the CPS→native lowering
builds the list *forward* with an O(1) continuation (tail-recursion-modulo-cons)
for every list builder, and owned-cons reuse recycles input cells for same-head
builders.

Codegen lowers only planner-authored contracts. It does not create alternate
spec bodies, probe for them, or infer destination arguments from continuation
captures.

### How `TupleFields` is granted

`TupleFields(N)` is legal when a destructuring continuation projects exactly the
`N` fields of its result and the producer returns an `N`-tuple on every path.
Both halves are cached per-fn in `ReturnCapability`:

- `returns_tuple_of_arity: Option<usize>` — every return path delivers a tuple
  of one arity (a `MakeTuple` or a frozen destination tuple), conjunctive across
  `Return`s and tail-call targets;
- `destructures_slot0_into_arity: Option<usize>` — the fn is a continuation
  whose slot-0 input is consumed purely by projecting all `N` fields, never used
  whole.

`capabilities::compute_return_capabilities` computes the whole
`ReturnCapabilities` (`HashMap<FnId, ReturnCapability>`) once over the static
call graph as greatest fixpoints (start optimistic, retract on a conflicting
path), and stores it on `ModulePlan`. The grant in `return_context.rs` reads it
in O(1) per call edge and never re-walks bodies. The shape is forwarded through
tail-recursive producers, so it survives the whole chain — quicksort's
`partition` and its clause helpers all deliver `tuple_fields(2)`, erasing the
`{lo, hi}` struct box.

## Physical Capabilities

Some planner facts are not source values: they are object-local permissions on
private runtime objects. The only one is owned-cons reuse.

The model layers cleanly so a physical fact never perturbs semantic
specialization:

- **semantic values** carry program meaning;
- **physical capabilities** carry object-local permissions (owned-cons reuse);
- **effect facts** (`EffectSummary`) say when an operation allocates, observes
  allocation, is externally observable, reaches the scheduler, halts, or reaches
  an opaque call. `ir_planner::effects::prim_effects` in `src/ir_planner/effects.rs`
  is the single operation effect classification, so capability validation and
  planner barriers read one source rather than a parallel publication rule or a
  standalone reuse-pruning pass and duplicate owned-cons capability lane.

`PhysicalCapability::OwnedConsReuse { head }` lets native codegen turn
`[h | new_tail]` into a reuse attempt for a source cons it owns, eliminating a
copied prefix. The capability is stored as a `PhysicalCapabilityFact { source,
capability }` on `FnIr::physical_capabilities`; the source slot rides an entry
parameter listed in `FnIr::physical_entry_params`. The planner spec dump renders
it as:

```text
physical_capabilities:
  owned_cons_source param=Var(C) head=Var(H)
```

The source slot is not a semantic parameter. `semantic_key` skips both
`physical_entry_params` and `ignored_entry_params` (the latter are source `_`
wildcard holes), so specialization keys ignore the physical slot by
construction.

The capability rides existing IR machinery:

- `src/fz_ir/mod.rs` exposes `physical_capabilities`, `physical_entry_params`,
  and `ignored_entry_params`, plus the builder/query helpers
  (`record_owned_cons_reuse_capability`, `owned_cons_reuse_source_for_head`).
- `src/ir_lower/cps.rs` transports `owned_cons_captures` through ordinary
  continuation-capture machinery; the source slots become physical
  params, not ignored semantic params.
- `src/ir_dce/mod.rs` owns liveness: live heads keep their source-cons param; a
  dead head drops the capability and its orphaned physical param.
- `src/ir_capture_norm/mod.rs` rewrites capture shapes and relies on DCE to
  preserve or drop the payload.
- `src/ir_codegen/support.rs` lowers the surviving fact through
  `emit_owned_cons_reuse_or_alloc`; codegen consumes validated facts and reads
  the reusable source straight from `physical_capabilities`.

### Runtime guard

The runtime alias bit is the cell-local guard, checked at the reuse attempt by
`Heap::reuse_or_alloc_list_cons_tail`:

- if the source cons `C` is unaliased, `relink_tail_if_unaliased` rewrites its
  tail in place and returns the same cell;
- if `C` is aliased, the runtime takes the fallback path and allocates a fresh cons
  with the same head and the requested tail.

An aliased reuse attempt is an allocation miss, not a panic.

Same-heap publication of a source cons sets the alias bit before reuse, by
walking the cons chain and marking each cell aliased
(`Heap::mark_published_ref_aliased`). Codegen emits this mark wherever a value
is published into long-lived heap state: a tuple field store, a closure or
continuation capture, or a map `put_ref`. Two boundaries are deliberately *not*
publications:

- **send.** The runtime deep-copies messages for cross-process and self-send, so
  the sender's current-process cells do not become aliased merely by being sent.
- **extern calls.** Extern arguments are not aliased; an extern that retains a
  value after returning must copy it.

## Codegen And Runtime

Codegen lowers each destination primitive directly.

- **Tuple field writes** go through typed struct setters — `struct_set_field`
  picks the int, float, or atom setter when the value's representation proves a
  raw lane, else the ref setter (which publishes first).
- **List destinations** lower to typed list-cons BIFs;
  `emit_owned_cons_reuse_or_alloc` routes a head with a reuse capability through
  `fz_list_reuse_or_cons_tail_ref`.
- **Map destinations** lower through `fz_map_dest_begin`, `fz_map_dest_put_*`,
  and `fz_map_dest_freeze`. These are destination operations, not a separate
  language-level construction model. Freeze keeps duplicate-key last-write-wins
  while publishing a canonical (sorted, deduped) map.

The interpreter executes destination primitives directly when handed
already-lowered IR (`DestTupleBegin` allocates a struct, `DestTupleSet` writes a
slot, `DestFreeze` returns the struct, and the list/map prims build through the
same runtime helpers). It does not run the destination-lowering pass itself —
only the codegen driver does. So `fz interp` and the scripted REPL fixture legs
are direct-IR baselines.

### Static aggregate storage

For a tuple whose fields are all known statically, codegen avoids the heap
entirely. `DestTupleBegin` records a `PendingStaticTupleDest` instead of
allocating. While walking the `DestTupleSet` chain:

- a compile-time scalar or read-only static-struct field is recorded into the
  pending slot;
- the first dynamic field forces materialization: codegen allocates the heap
  struct, replays the recorded static fields through the struct setters, and
  continues on the heap path.

At `DestFreeze`, a still-pending destination emits one schema-valid static
struct data symbol and returns a `ValueKind::STRUCT` ref to it; a materialized
one returns the heap struct. This is a storage representation choice for
already-proven construction. It infers no new construction permission and does
not rewrite the plan.

### GC

All destination storage lives in the process-private heap. GC safety comes from
ordinary roots: a destination-built value live across a call, receive, or yield
must be in normal frame, closure, or continuation state. Init tokens are
compile-time proof only — never scheduler state, closure captures, or heap
words.

Native continuations may be stack-backed lazy descriptors while execution stays
synchronous; this does not change destination ownership. A descriptor is
materialized into a normal closure before it can become scheduler-visible or
heap-captured. See
[`lazy-continuation-materialization.md`](lazy-continuation-materialization.md).

## Policy And Pinned Signal

Destination semantics live in IR, not only in codegen: construction intent is
visible, verified, and typed before any backend sees it. Native JIT/AOT paths
run `ir_dest::lower_destinations` before codegen; the interpreter runs already
lowered IR. Codegen never manufactures destination or demand facts. A new
destination shape must be exposed in the data model, validated by the planner
consistency harness, and observed through telemetry before codegen consumes it.

Allocation floors pin that the optimizations hold; a regression means a
capability was dropped. The native (JIT/AOT) `expected` fixtures pin:

```text
quicksort:             list_cons_allocs = 11,  closure_allocs = 0  (176 bytes)
enum_list_allocations: list_cons_allocs = 5,   closure_allocs = 1
enum_reduce_suspend:                            closure_allocs = 1
```

Quicksort reaches its floor with eleven input conses and zero struct or closure
allocations — `tuple_fields(2)` erases the partition struct box, and forward
list-build plus owned-cons reuse keep cons allocation minimal — with no
list-tail delivery anywhere.
