# Destination Passing

Destination passing makes construction explicit in IR. A destination is an
unpublished heap object being initialized; an init token is compile-time
permission to perform the next write. Once frozen, the value is ordinary
immutable data and no later primitive may mutate it.

## Pieces

`fz_ir::Prim` owns the visible IR vocabulary:

- `DestTupleBegin { token, arity }` allocates an unpublished tuple destination
  and mints the first token.
- `DestTupleSet { dest, token, index, value, next }` consumes one token, writes
  one tuple field, and produces the next token.
- `DestFreeze { dest, token }` consumes the final token and publishes the
  destination as a normal value.
- `DestListBegin { token }` mints the first token for a destination-built list
  chain.
- `DestListCons { token, head, tail, next }` consumes one token and constructs
  one immutable cons cell from a head and a known tail. `tail = None` means the
  empty-list sentinel.
- `DestListFreeze { list, token }` consumes the final list token and publishes
  the built list.
- `DestMapBegin { token, base, extra }` allocates a map builder. `base` seeds
  the builder from an existing immutable map for update-shaped construction;
  `extra` is the number of appended key/value pairs.
- `DestMapPut { map, token, key, value, next }` consumes one token and appends
  one key/value pair to the builder.
- `DestMapFreeze { map, token }` consumes the final map token, sorts/dedups the
  builder entries with the runtime map ordering, and publishes the immutable
  sorted-array map.

`ir_dest::verify_module` owns the static contract. It rejects duplicate token
definitions, undefined token uses, token reuse, out-of-order tuple fields, arity
overflow, and freezing before every field has been initialized.

`ir_dest::lower_tuple_destinations` owns the current tuple rewrite. It runs near
the end of codegen and interpreter preparation, after the reducer/optimizer/DCE
have produced the executable IR shape. Each surviving `MakeTuple` becomes
`Begin`, one `Set` per element in field order, then `Freeze`.

`ir_dest::lower_list_destinations` owns the current list rewrite. Each surviving
non-empty `MakeList` becomes `DestListBegin`, one `DestListCons` per element
from right to left, then `DestListFreeze`. Empty-list literals remain the
empty-list sentinel path.

`ir_dest::lower_map_destinations` owns the current map rewrite. Each surviving
`MakeMap` or `MapUpdate` becomes `DestMapBegin`, one `DestMapPut` per known
entry in source order, then `DestMapFreeze`. Runtime freeze preserves duplicate
key last-write-wins behavior while keeping the published map canonical.

`ir_codegen` owns typed field initialization. Tuple destinations allocate the
same canonical tuple schemas as `MakeTuple`. Field writes use raw int, float,
and atom setters when the local binding already proves that lane; only unknown
or heap values go through the generic ref setter. List destinations lower to the
same typed list-cons BIFs as the old literal path, so raw int, float, and atom
heads do not need scalar boxes. Map builders write raw/kind parts directly when
both key and value have local representation facts; unknown values use the
generic ref writer.

`runtime` owns the heap writes. The runtime setters write `AnyValue` slots in
the process-private heap. GC safety comes from existing frame and continuation
capture tracing: any destination that is live across a call, receive, or yield
must be held in an ordinary GC-visible value slot.

## Dataflow

For a tuple literal `{1, x}` after tuple DP:

```text
dest = DestTupleBegin(tok0, arity=2)
_    = DestTupleSet(dest, tok0, field=0, value=1, next=tok1)
_    = DestTupleSet(dest, tok1, field=1, value=x, next=tok2)
out  = DestFreeze(dest, tok2)
```

The token never becomes runtime data. It is only the verifier's proof that the
destination is written linearly before publication.

For a list literal `[a, b | tail]` after list DP:

```text
_  = DestListBegin(tok0)
c1 = DestListCons(tok0, head=b, tail=tail, next=tok1)
c0 = DestListCons(tok1, head=a, tail=c1, next=tok2)
xs = DestListFreeze(c0, tok2)
```

The runtime still allocates each cons with its head and tail initialized in one
typed BIF call; the tokenized IR is the construction proof.

For a map update `%{m | a: 3, c: 4}` after map DP:

```text
b  = DestMapBegin(tok0, base=m, extra=2)
_  = DestMapPut(b, tok0, key=:a, value=3, next=tok1)
_  = DestMapPut(b, tok1, key=:c, value=4, next=tok2)
out = DestMapFreeze(b, tok2)
```

The builder is represented as a heap map with null-tagged unused slots, so a
partially-filled builder remains traceable. Freeze usually sorts and publishes
the builder in place; when duplicate keys shrink the entry count, freeze
allocates the final canonical map once.

## Policy

Do not hide destination behavior only in codegen. Construction intent must be
visible in IR first, verified, then lowered by the interpreter/JIT/AOT paths.

Run tuple destination lowering after the optimizer for now. Earlier lowering
copies token ids through inlining unless inlining learns to remap init tokens;
post-optimization lowering keeps token ownership local to the final executable
IR.

After destination lowering, codegen retypes the transformed module so dispatch
metadata matches the final IR. It may merge narrower pre-DP facts only for the
exact same spec key; broad same-function merges can resurrect facts for specs
that DCE no longer emits.

## Proof Gates

Gate this model with:

- `cargo test ir_dest`
- `cargo test tuple`
- `cargo test list`
- `cargo test map`
- `cargo test mid_flight_gc_preserves_destination_built_tuple_arg`
- `cargo test mid_flight_gc_preserves_destination_built_list_arg`
- `cargo test mid_flight_gc_preserves_destination_built_map_arg`
- `cargo test --test fixture_matrix nested_tuple_producer`
- `cargo clippy --workspace --all-targets -- -D warnings`
