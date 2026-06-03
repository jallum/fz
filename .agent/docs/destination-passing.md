# Destination Planning

Destination planning answers one question: where may a value be built before it
is published as ordinary immutable data?

The active destination model is local construction through explicit IR
destination primitives. Return delivery is a separate call-edge ABI contract
owned by the planner; it is not a backend hint and it does not create hidden
destination bodies.

See [`dispatch-as-planner-output.md`](dispatch-as-planner-output.md) for the
planner-owned call-edge contract and
[`single-authoritative-plan.md`](single-authoritative-plan.md) for the
one-plan pipeline rule.

## Big Idea

The compiler should know where a value is going before it builds the value.
When the destination is typed, construction can happen directly in that context
without changing language semantics:

- a tuple literal can write fields into unpublished tuple storage and freeze
  once;
- a list literal can build cons cells through a linear token chain;
- a map literal or update can collect writes in unpublished storage and freeze
  once.

A destination is an unpublished construction location. An init token is the
erased linear IR identity that proves which write/freeze operation may happen
next. Once a destination is frozen, the result is ordinary immutable data and
no later IR primitive may mutate it.

The simplifying rule is ownership of proof: IR carries explicit construction
intent, the planner types the construction through erased token facts, the
verifier checks token coherence, and codegen lowers those facts mechanically.
Backend shape recognition is not proof.

## Active Families

There is one active destination-planning family:

- init-token destinations in `fz_ir::Prim`, used for local tuple/list/map
  construction.

Two adjacent mechanisms are deliberately not destination-planning families:

- return delivery in `ir_planner::fn_types::ReturnContract`, which describes
  how a call edge returns but does not create hidden construction storage;
- physical capabilities such as owned-cons reuse, which are object-local
  permissions carried separately from semantic values.

Init tokens are compile-time facts attached to `InitTokenId`, in the same broad
family as:

- `Var -> Ty` facts in `SpecPlan.vars` and block environments;
- `CallsiteId -> CallEdgePlan` facts in `SpecPlan.call_edges`;
- `BlockId -> reachable/dead-branch` facts in `SpecPlan.reachable_blocks` and
  `SpecPlan.dead_branches`.

The token fact is local to `ir_planner::type_fn`; it is not persisted in
`SpecPlan` because codegen needs only the final value type of ordinary vars.

## Return Delivery Boundary

`SpecKey` includes a `ReturnDemand`, but `ReturnDemand` is not a semantic body
identity. Semantic return payloads and materialized executable bodies are keyed
by `BodyKey` (`FnId + input`), while `SpecKey.demand` can describe an edge ABI.

The executable call-edge fact is `ReturnContract`: it pairs the selected target
`SpecKey` with a `ReturnStrategy` that makes that edge legal. Codegen lowers
only planner-authored contracts; it does not create alternate spec bodies,
probe for alternate bodies, or infer destination arguments from continuation
captures.

Current executable return strategies are:

- `Value`: ordinary material return;
- `TupleFields(N)`: tuple-field delivery to a continuation;
- `ForwardedDemand(demand)`: a tail-call edge forwards the caller's demand.

The ordinary planner path for direct calls, tail calls, and continuation hops
selects `Value`. `TupleFields(N)` remains an explicit ABI capability for
callback-style edges and continuation delivery. There is no list-tail
return-delivery axis in the data model.

If destination-style return delivery is reintroduced, it must be represented as
explicit planner output with telemetry and consistency checks. Codegen must
receive concrete instructions, not derive them from backend shape.

## IR Vocabulary

`fz_ir::Prim` owns destination operations:

- `DestTupleBegin { token, arity }` allocates an unpublished tuple destination
  and defines the first token.
- `DestTupleSet { dest, token, index, value, next }` consumes one token, writes
  one tuple field, and defines the next token.
- `DestFreeze { dest, token }` consumes the final tuple token and publishes the
  tuple value.
- `DestListBegin { token }` defines the first token for a destination-built
  list chain.
- `DestListCons { token, head, tail, next }` consumes one token, constructs one
  cons cell from `head` and a known tail, and defines the next token.
- `DestListFreeze { list, token }` consumes the final list token and publishes
  the built list.
- `DestMapBegin { token, base, extra }` allocates an unpublished map
  destination.
- `DestMapPut { map, token, key, value, next }` consumes one token, sets one
  key/value pair in the unpublished map destination, and defines the next
  token.
- `DestMapFreeze { map, token }` consumes the final map token, canonicalizes
  the map ordering/deduplication, and publishes the immutable map value.

## Lowering

`ir_dest::lower_tuple_destinations` rewrites each surviving `MakeTuple` to:

```text
dest = DestTupleBegin(tok0, arity=N)
_    = DestTupleSet(dest, tok0, index=0, value=v0, next=tok1)
...
out  = DestFreeze(dest, tokN)
```

`ir_dest::lower_list_destinations` rewrites each surviving non-empty
`MakeList` from right to left:

```text
_  = DestListBegin(tok0)
c1 = DestListCons(tok0, head=b, tail=tail, next=tok1)
c0 = DestListCons(tok1, head=a, tail=c1, next=tok2)
xs = DestListFreeze(c0, tok2)
```

Empty-list literals remain the empty-list sentinel.

`ir_dest::lower_map_destinations` rewrites each surviving `MakeMap` or
`MapUpdate` to:

```text
m0  = DestMapBegin(tok0, base=base_or_none, extra=N)
_   = DestMapPut(m0, tok0, key=k0, value=v0, next=tok1)
...
out = DestMapFreeze(m0, tokN)
```

Runtime freeze preserves duplicate-key last-write-wins semantics while keeping
the published map canonical.

Destination lowering runs after planner-owned executable body selection, which
keeps init-token ownership local to the lowered body handed to codegen.

## Verification

`ir_dest::verify_module` owns structural correctness:

- token definitions are unique;
- each token is consumed at most once;
- tuple fields are in bounds and written at most once;
- tuple freeze requires every field to be initialized;
- tuple destinations are not written after freeze.

Tuple verifier transitions are factored through shared helpers in
`src/ir_dest.rs`; the planner uses those same transition helpers with `Ty`
payloads so verifier and planner do not drift.

## Typing

`ir_planner::type_fn` folds destination statements with erased token facts
before falling back to ordinary `type_prim` handling.

Tuple token facts carry initialized field slots. `DestFreeze` publishes
`Types::tuple(fields)` from the complete token fact, not from the opaque
destination handle type.

List token facts carry the current list value type. `DestListCons` binds the
cons var to the precise non-empty list type, and `DestListFreeze` publishes the
token fact with a value-type fallback for malformed IR.

Map token facts carry the current map value type. `DestMapBegin` seeds the fact
from `base` or `Types::map(&[])`; `DestMapPut` refines static keys with
`var_as_map_key` and `Types::refine_map_field`; dynamic keys widen to
`map_top()`. `DestMapFreeze` publishes the token fact.

Malformed destination IR should not panic the planner. Verified codegen should
not see malformed IR, but the planner falls back conservatively and leaves
diagnostics to the verifier.

## Physical Capabilities

Some planner facts are not source values. They are object-local permissions on
private runtime objects, chiefly owned-cons reuse.

A physical capability must not affect semantic specialization.
`src/ir_planner/effects.rs` classifies operation effects: whether an operation
allocates, observes allocation, is externally observable, reaches the scheduler,
or halts. Capability validation reads that classifier rather than carrying a
parallel publication rule.

Owned-cons reuse eliminates copied prefixes when the compiler has a source-cons
capability for a projected head. The source slot is not a source value and is
not modeled as an ignored semantic parameter. The spec dump exposes the
capability:

```text
physical_capabilities:
  owned_cons_source param=Var(C) head=Var(H)
```

The physical parameter is not part of semantic specialization, but it gives
native codegen the object-local capability needed to turn `[h | new_tail]` into
a reuse attempt for `C`. The runtime alias bit remains the cell-local guard: if
`C` is still unaliased, the helper relinks it in place; if `C` was marked
aliased, the helper allocates a fresh cons with the same head and requested
tail. An aliased reuse attempt is an allocation miss, not a user-visible panic.

The capability rides existing IR machinery:

- `src/fz_ir/mod.rs` exposes `physical_capabilities` for object-local facts,
  `physical_entry_params` for entry slots that carry physical facts, and
  `ignored_entry_params` only for source wildcard holes.
- `src/ir_lower/cps.rs` transports `owned_cons_captures` through ordinary
  continuation-capture machinery.
- `src/ir_dce/mod.rs` owns capability liveness.
- `src/ir_capture_norm/mod.rs` rewrites capture shapes and relies on DCE to
  preserve or drop capability payloads.
- `src/ir_codegen/support.rs` lowers the surviving fact through
  `emit_owned_cons_reuse_or_alloc`.

The standalone reuse-pruning pass and duplicate owned-cons capability lane have
been removed. Codegen reads reusable source objects straight from
`physical_capabilities`, and semantic specialization ignores only the entry
params listed in `physical_entry_params`.

## Runtime And GC

`ir_codegen` lowers tuple field writes through typed struct setters when local
representation facts prove raw int, float, or atom lanes. List destinations
lower to typed list-cons BIFs. Map destinations lower through
`fz_map_dest_begin`, `fz_map_dest_put_*`, and `fz_map_dest_freeze`; these helper
names are destination operations, not a separate language-level construction
model.

All destination storage lives in the process-private heap. GC safety comes from
ordinary roots: if a destination-built value is live across a call, receive, or
yield, it must be in normal frame, closure, or continuation state. Init tokens
are compile-time proof only; they are not scheduler state, closure captures, or
heap words.

Native continuations may be represented by stack-backed lazy descriptors while
execution stays synchronous. That does not change destination ownership:
destination facts still come from IR and planner facts, and a descriptor is
materialized into a normal closure before it can become scheduler-visible or
heap-captured. See
[`lazy-continuation-materialization.md`](lazy-continuation-materialization.md).

## Policy

Destination semantics live in IR, not only in codegen. Construction intent is
visible in IR, verified, and typed through erased token facts. Native JIT/AOT
paths run `ir_dest::lower_destinations` before codegen. The `fz interp` and
scripted REPL fixture legs are direct-IR baselines: they execute destination
primitives when handed already-lowered IR, but the CLI interpreter does not run
the destination-lowering pass itself.

Codegen never manufactures destination or demand facts. If a future optimizer
needs a new destination shape, the data model must expose it before codegen,
the planner consistency harness must validate it, and tests should observe the
fact through telemetry wherever possible.

## Proof Gates

Use these gates when touching destination planning:

- `cargo test ir_dest`
- `cargo test ir_planner`
- `cargo test tuple`
- `cargo test list`
- `cargo test map`
- `cargo test --test fixture_matrix`
- `cargo clippy --workspace --all-targets -- -D warnings`
