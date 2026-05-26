# Destination Passing

Destination passing makes container construction explicit in IR. A destination
is an unpublished construction location; an init token is the erased linear IR
identity that proves which write/freeze operation may happen next. Once a
destination is frozen, the result is ordinary immutable data and no later IR
primitive may mutate it.

There are two destination-passing families:

- init-token destinations in `fz_ir::Prim`, used for local tuple/list/map
  construction;
- return-demand destinations in `ir_typer::fn_types::ReturnDemand`, used when
  the typer proves that a call result can be delivered into a typed context
  without first materializing the ordinary return value.

Both families keep the same ownership rule: the compiler proves a private,
unpublished construction context, codegen lowers that context, and the
published result remains immutable.

Init tokens are not runtime values. They are compile-time facts attached to
`InitTokenId`, in the same broad family as:

- `Var -> Ty` facts in `FnTypes.vars` and block environments.
- `CallsiteId -> SpecKey` dispatch facts in `FnTypes.dispatches`.
- `BlockId -> reachable/dead-branch` facts in `FnTypes.reachable_blocks` and
  `FnTypes.dead_branches`.
- `SpecKey.demand` facts such as tuple-field delivery and list-tail context.

The token fact is local to `ir_typer::type_fn`; it is not persisted in
`FnTypes` because codegen needs only the final value type of ordinary vars.

## Return Demand

`SpecKey` includes a `ReturnDemand`. This is a typed compile-time capability,
not a runtime side channel. The typer chooses demanded variants while walking
specific callsites; codegen must implement the selected capability and must not
invent a different variant by guessing from function names.

`ReturnDemand` is factored into two axes:

- delivery: how the callee delivers the return value (`Value` or
  `TupleFields(N)`);
- context: what result context is already available at the return edge
  (`None` or `ListTail(tail_ty)`).

The central invariant is that demand follows a specific return edge/result
hole, not the whole caller spec. A caller spec can contain more than one call,
and different calls in that spec can have different return uses. The durable
facts are:

- `FnTypes.return_uses`, keyed by `CallsiteId`, records the typed return-use
  fact for each call edge;
- `FnTypes.list_tail_plans`, keyed the same way, records the executable
  ListTail plan when a return-use fact needs lowering.

Current rendered forms:

- `Value` is the ordinary material return.
- `TupleFields(N)` means a tuple result is delivered to the continuation as
  `N` Tail-CC values. This removes the tuple struct allocation for shapes such
  as `partition(...) -> {lo, hi}` when the continuation immediately projects
  the fields.
- `ListTail(tail_ty)` means the native callee receives a hidden physical list
  tail destination. Returning `[]` delivers that destination directly; returning
  a list literal builds its cons cells in front of the destination.
- `TupleFields(N)` delivery can compose with `ListTail(tail_ty)` context: the
  continuation receives tuple fields and also carries an appended hidden
  list-tail capture. This is rendered as
  `tuple_fields(N, list_tail(tail_ty))`.

ListTail is typed context passing. For the source shape:

```text
append(qsort(lo), [pivot | qsort(hi)])
```

the demanded native path executes the equivalent context:

```text
hi_tail = qsort_into(hi, outer_tail)
pivot_tail = [pivot | hi_tail]
qsort_into(lo, pivot_tail)
```

This follows the FP2/TRMReC idea of making the evaluation context explicit and
defunctionalized, but it does not use destructive in-place mutation. Every cons
cell is still allocated as an immutable BEAM-style list cell on the owning
process heap; destination passing only chooses the tail that the new cells point
at.

ListTail scheduling is legal only when the typer can prove that moving work
does not cross an observable barrier. The current gates reject contexts that
contain observable externs, scheduler-visible operations, receives, closure
calls, allocation-stats readers such as `Process.heap_alloc_stats()`, and
print-like operations. Allocation by itself is not source-observable, but
allocation becomes observable in the presence of allocation-stat reads.

The pinned evidence is `fixtures/quicksort_stats`: native JIT/AOT output now
keeps `list_cons_allocs = 48`, `list_cons_bytes = 768`,
`struct_allocs = 0`, and headline `heap_bytes = 768`.

## IR Vocabulary

`fz_ir::Prim` owns the destination operations:

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
  `tail = None` means the empty-list sentinel.
- `DestListFreeze { list, token }` consumes the final list token and publishes
  the built list.
- `DestMapBegin { token, base, extra }` allocates an unpublished map
  destination. `base` seeds it from an existing immutable map for update-shaped
  construction; `extra` is the number of additional key/value writes.
- `DestMapPut { map, token, key, value, next }` consumes one token, sets one
  key/value pair in the unpublished map destination, and defines the next
  token.
- `DestMapFreeze { map, token }` consumes the final map token, canonicalizes
  the map ordering/deduplication, and publishes the immutable map value.

## Lowering

`ir_dest::lower_tuple_destinations` rewrites each surviving `MakeTuple` to:

```text
dest = DestTupleBegin(tok0, arity=N)
_    = DestTupleSet(dest, tok0, field=0, value=v0, next=tok1)
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

## Verification

`ir_dest::verify_module` owns structural correctness:

- token definitions are unique;
- each token is consumed at most once;
- tuple fields are in bounds and written at most once;
- tuple freeze requires every field to be initialized;
- tuple destinations are not written after freeze.

Tuple verifier transitions are factored through shared helpers in
`src/ir_dest.rs`; the typer uses those same transition helpers with `Ty`
payloads so verifier and typer do not drift.

## Typing

`ir_typer::type_fn` folds destination statements with erased token facts before
falling back to ordinary `type_prim` handling.

Tuple token facts carry initialized field slots. `DestFreeze` publishes
`Types::tuple(fields)` from the complete token fact, not from the opaque
destination handle type. This is what prevents tuple DP from turning
`partition(...) -> {lo, hi}` into `any`.

List token facts carry the current list value type. `DestListCons` still binds
the cons var to the precise non-empty list type, and `DestListFreeze` publishes
the token fact with a value-type fallback for malformed IR.

Map token facts carry the current map value type. `DestMapBegin` seeds the fact
from `base` or `Types::map(&[])`; `DestMapPut` refines static keys with
`var_as_map_key` and `Types::refine_map_field`; dynamic keys widen to
`map_top()`. `DestMapFreeze` publishes the token fact.

Malformed destination IR should not panic the typer. Verified codegen should
not see malformed IR, but the typer falls back conservatively (`any`, `nil`, or
the visible value type) and leaves diagnostics to the verifier.

## Runtime And GC

`ir_codegen` lowers tuple field writes through typed struct setters when local
representation facts prove raw int, float, or atom lanes. List destinations
lower to typed list-cons BIFs. Map destinations lower through
`fz_map_dest_begin`, `fz_map_dest_put_*`, and `fz_map_dest_freeze`; these helper
names are destination operations, not a separate language-level construction
model.

All destination storage lives in the process-private heap. GC safety comes from
ordinary roots: if a destination-built value is live across a call, receive, or
yield, it must be in normal frame/closure continuation state. Init tokens are
compile-time proof only; they are not scheduler state, closure captures, or
heap words.

## Policy

Do not hide destination semantics only in codegen. Construction intent must be
visible in IR, verified, typed through erased token facts, then lowered by the
interpreter/JIT/AOT paths.

Do not make ReturnDemand a backend-only heuristic. `FnTypes.dispatches`,
`FnTypes.return_uses`, `FnTypes.list_tail_plans`, and `SpecKey.demand` are the
authoritative typer output. Codegen may lower only those typer-authored ABI and
context facts. Compatibility sibling lookups in codegen are permitted only when
they resolve an already-registered spec; they must not create a new demand
variant or infer demand from backend closure/capture shapes.

Current deletion audit:

- no `TupleFieldsListTail` enum variant exists; tuple-field delivery plus
  ListTail context is represented by the two-axis `ReturnDemand`;
- `src/ir_codegen` no longer mutates dispatch keys with `key.demand = ...`;
- `src/ir_codegen/terminator.rs` no longer recognizes ListTail context by
  indexing `continuation.captured[...]`.

Run destination lowering after the optimizer for now. Earlier lowering would
require every inliner/rewriter to remap init tokens correctly; post-optimizer
lowering keeps token ownership local to executable IR.

Do not resurrect broad same-function pre-DP fact merging. A previous quicksort
regression showed why: broad merging can attach facts to specs that DCE no
longer emits. The correct fix is preserving constructor precision through the
lowered IR with token facts.

## Proof Gates

Use these gates when touching destination passing:

- `cargo test ir_dest`
- `cargo test ir_typer`
- `cargo test tuple`
- `cargo test list`
- `cargo test map`
- `cargo test --test fixture_matrix quicksort`
- `cargo test --test fixture_matrix dump_budgets`
- `cargo clippy --workspace --all-targets -- -D warnings`
