# Destination Passing

Destination passing makes container construction explicit in IR. A destination
is an unpublished construction location; an init token is the erased linear IR
identity that proves which write/freeze operation may happen next. Once a
destination is frozen, the result is ordinary immutable data and no later IR
primitive may mutate it.

Init tokens are not runtime values. They are compile-time facts attached to
`InitTokenId`, in the same broad family as:

- `Var -> Ty` facts in `FnTypes.vars` and block environments.
- `CallsiteId -> SpecKey` dispatch facts in `FnTypes.dispatches`.
- `BlockId -> reachable/dead-branch` facts in `FnTypes.reachable_blocks` and
  `FnTypes.dead_branches`.

The token fact is local to `ir_typer::type_fn`; it is not persisted in
`FnTypes` because codegen needs only the final value type of ordinary vars.

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
