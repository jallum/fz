# Any Values

## The Idea

Every fz value — integer, float, atom, list, map, tuple/struct, closure,
bitstring, ProcBin, resource — is handled at runtime boundaries as one opaque
word:

```text
AnyValueRef = one word that says "here is a value"
```

The word carries a 4-bit tag (what kind) and an address (where the payload is).
Scalar refs point at a scalar payload word; heap refs point at a heap object. A
heap reference is not a separate idea — it is the heap-object subset of
`AnyValueRef`. The interpreter, REPL, JIT, and AOT paths all pass values through
this one shape, so spawn, receive, matching, and heap reads behave the same on
every path.

```text
Int ref      -> i64 payload word        Map ref      -> map object
Float ref    -> f64 payload word        List ref     -> cons cell
Atom ref     -> atom-id payload word     Struct ref   -> tuple/struct object
                                        Closure ref  -> closure object
                                        Bitstring/ProcBin ref -> binary object
                                        Resource ref -> resource object
```

`AnyValueRef` (`runtime/src/any_value.rs`) is `#[repr(transparent)]` over a `u64`
and is opaque: callers do not pack, unpack, or dereference it by hand. The type
owns packing, projection, and the platform difference behind the word.

## The Pieces And What They Own

- **`AnyValueRef`**: the public word. Owns packing/unpacking and projection.
  `tag()` returns a `ValueKind`; `load_int`/`load_float`/`load_atom` read scalar
  payloads; `list_addr`/`map_addr`/`struct_addr`/… project heap refs to a
  cleared address (each checks the tag and errors on mismatch).
- **`ValueKind`**: the tag, one byte. `is_heap()` (List..Resource) and
  `is_scalar()` (Int/Float/Atom) classify it.
- **`AnyValue`**: the by-value enum a host caller decodes a ref into —
  `Null`, `EmptyList`, `Int(i64)`, `Float(u64)`, `Atom(u32)`, `HeapRef(AnyValueRef)`.
  A scalar `AnyValue` has no address; `ref_word()` panics on a scalar because a
  scalar needs object-local storage before it can become a ref.
- **Container object-local metadata**: each heap object stores payload words
  plus its own kind bytes (see Container Storage). This is *not* a reusable
  `{value, kind}` carrier — there is no public value model other than the ref.
- **The `fz_*` runtime ABI** (`runtime/src/ir_runtime.rs`): the C entry points
  generated code calls to read, build, and project values.

## The Public Ref ABI

Generated code handles values only through these entry points. A few examples:

```text
fz_ref_tag(ref)                      -> tag byte
fz_ref_load_int / _float / _atom(ref)
fz_map_get_ref(process, map, key)    -> ref
fz_map_count(map) / fz_map_entry_key(map, i) / fz_map_entry_value(map, i)
fz_list_head_ref(list) / fz_list_tail_ref(list)
fz_struct_get_field_ref(process, struct, field_offset)
fz_binary_concat(process, left, right)
```

**Dynamic reads return refs into existing storage, not copies.**
`fz_map_get_ref`, `fz_map_entry_key`/`_value`, `fz_list_head_ref`, and
`fz_struct_get_field_ref` build a ref over the slot already living in the
container. For a scalar slot the returned ref points straight at that payload
word (`any_value_ref_from_storage`); for a heap slot it carries the slot's
heap pointer. `Enumerable.Map` (`src/modules/runtime_library/map.fz`) is plain
fz source that declares `fz_map_count`, `fz_map_entry_key`, `fz_map_entry_value`
as externs and folds over the map's canonical sorted entries; the tuple/list it
builds copies those values into fresh containers before publishing them.

`fz_binary_concat` validates byte-aligned binary inputs, copies their bytes into
the caller process heap through `Heap::alloc_bitstring`, and tags the result
`ProcBin` past `SHARED_BIN_THRESHOLD_BYTES` (64) or `Bitstring` below it — so
large results land on the shared-binary path on their own.

**Typed fast reads** are fused helpers for callers the typer already proved the
shape of. They project then load, and `.expect()` the projection, so they panic
on a mismatched ref rather than inventing a second value model:

```text
fz_map_get_int(map, key)   -> i64
fz_map_get_float(map, key) -> f64
fz_map_get_atom(map, key)  -> atom id
```

**Typed writes** hand a known scalar straight into a container's compact
object-local layout, with no detour through a built scalar ref:

```text
fz_map_put_int(process, map, key, value_i64)
fz_list_cons_int(process, head_i64, tail)
```

The `*_put_ref` / `*_cons_ref` paths are for already-dynamic refs. They call
`reject_scalar_ref_write` and panic on a scalar ref, so a scalar always travels
the typed-write path and the representation stays honest.

### Walkthrough: read a value out of a map

A map holds `:answer => 42`. The 42 lives in the map's value storage. The read
hands back a ref over that slot:

```text
value_ref = fz_map_get_ref(map_ref, atom_answer_ref)
  value_ref.tag()      = Int
  value_ref points at  the stored i64 slot
fz_ref_load_int(value_ref) -> 42
```

If the map holds another map at `:child`, the same call returns a `Map` ref
directly — no two-part `{address, kind}` result is needed:

```text
child_ref = fz_map_get_ref(parent_map_ref, atom_child_ref)
  child_ref.tag() = Map  ->  child map object
```

## Generated-Code Value Lanes

Generated code keeps a value in the narrowest representation the typer can
prove. The codegen-side enum is `CodegenValue` (`src/ir_codegen/value.rs`); the
ABI-side enum threaded through call signatures is `ArgRepr`
(`src/ir_codegen/repr.rs`). The lanes:

```text
ValueRef  // one AnyValueRef word; the only `any`-shaped lane
RawInt    // proven i64
RawF64    // proven f64
RawAtom   // proven atom id
Condition // raw i1 from a comparison/type-test whose result is only branched on
```

`ArgRepr::from_ty` picks the lane: float -> `RawF64`, integer -> `RawInt`,
atom-subtype -> `RawAtom`, else `ValueRef`. `CodegenValue` adds `AnyRef` (an
`any` ref value) and `Known { payload, kind }` (a compile-time-constant scalar);
both report `ArgRepr::ValueRef`. Every lane has `abi_arity() == 1`: a value is
always one machine word across a call boundary, never split into payload + kind.

Boxing happens only where a typed lane meets an `any` boundary.
`CodegenFn::coerce_binding_to` is the one seam:

```text
RawInt   -> ValueRef : box_int_for_any
RawF64   -> ValueRef : box_float_for_any
RawAtom  -> ValueRef : box_atom_for_any
Condition-> ValueRef : select true/false atom, then box
ValueRef -> RawInt/RawF64/RawAtom : unbox via the ref API
matching lanes : pass through
```

So `send(pid, 42)`, where `send` takes `any`, boxes 42 because it crosses into
`any`, then passes one `ValueRef(Int)` word. Copying the bits of a
`ValueRef(Int)` straight into a `RawInt` slot is never valid: that word is a ref,
not the integer payload. The same coercion rule covers call arguments,
continuation arguments, and typed frame slots.

## Tags And Platform Packing

`ValueKind` tags are semantic and platform-independent (`runtime/src/any_value.rs`):

```text
0  Null        4  Closure       7  Resource      14 Float
1  List        5  Bitstring     13 Int           15 Atom
2  Map          6  ProcBin
3  Struct
```

`8` (`TAG_FWD`) is the Cheney forwarding marker, not a value; `9`–`12` are
unused; `ValueKind::new` rejects all of them. The empty list is `List` with a
null address (`AnyValueRef::empty_list`). Object storage also uses an
`EMPTY_LIST` tail sentinel (`0x8`, an address inside the OS-reserved unmapped
page 0, distinct from `nil`), but that sentinel is internal list-tail
plumbing, not the public tagged-pointer form of `[]`.

The *bits* that hold the tag are per-arch, owned by `AnyValueRefPacking`:

```text
arm64 (TBI):          tagged = address | (tag << 56)
x86_64 (canonical):   tagged = address | (tag << 57)
```

`fz_ref_tag` returns the same semantic tag on both, so callers never see the
difference.

Compiler-emitted pointer refs follow the same split, in
`src/ir_codegen/closure.rs` and `src/ir_codegen/fn_ctx.rs`. On arm64/TBI a fresh
stack/heap pointer is tagged by OR-ing the top-byte tag word directly, with no
address-mask clear. On x86_64 canonical refs the high bits are cleared with
`ishl_imm` then `ushr_imm` before OR-ing the tag word. Keeping codegen on
`AnyValueRefPacking` rather than a hardcoded mask is what keeps
`fz dump --emit clif` aligned with the runtime packing model.

## Container Storage

Containers *appear* to store `AnyValueRef`s when dynamic code reads them, but
that is a projection rule, not the physical layout. Each object holds payload
words plus its own packed kind metadata, and the ref API reconstructs a ref on
read:

```text
List cons (16 bytes): head payload word
                      link word = tail address + head-kind nibble + alias bit
Map:                  count, one packed key/value kind byte per entry,
                      then key payload words, then value payload words
Closure:              schema id + flags (captured count + halt kind),
                      code pointer, capture payload words, capture kind bytes
```

The list link's **alias bit** is a conservative cell-local reuse guard. A cons
is the single owner of its tail link until it is *published*; publication turns
later destructive rewrites of that cell into a fresh allocation fallback. The
bit is set (or a reuse capability simply not recorded) when a cell escapes the
single owned rewrite path: stored in another heap object, captured in a closure
or scheduler-visible continuation, or carried across a barrier where allocation
timing becomes observable. Native call lowering
(`mark_retained_call_args_as_published`) marks an argument the caller both passes
to a callee and keeps in the continuation, which is what stops `xs |> reverse();
xs |> map()` from letting the first call rewrite the list the continuation still
reads.

Reuse helpers stay total for valid inputs: an unaliased source cons may be
relinked in place; an aliased one takes the fallback path and allocates a fresh cons
with the same head and the requested tail (`reuse_or_alloc_list_cons_tail`).
Passing a value to an extern
does not publish it (an extern that retains a value past the call must copy it).
Cross-process send and self-send are copy boundaries, not alias boundaries: the
sender's current cells need not be marked, because the receiver gets a fresh
unaliased graph. The bit is one-way within a heap — later local code may still
read a published cell, but destructive reuse falls back to allocation.

## GC: Roots, Edges, And Lifetime

The process heap is a moving Cheney collector (`runtime/src/heap/gc/`). An
`AnyValueRef` can point into it, so a bare ref is a *temporary*: it must not
survive an allocation, a yield, a GC, or any runtime call that may allocate or
yield, unless it has been stored in a traced root.

GC copies each reachable object as a whole unit, then follows only the payload
slots whose object-local kind byte says `is_heap()`
(`cheney_trace_list`/`_map`/`_struct`/`_closure`/`_resource`):

```text
copy:   every reachable object moves as a unit
follow: only heap-shaped payload words become child roots
```

Heap-object refs (`Map, List, Struct, Closure, Bitstring, ProcBin, Resource`)
are followed as edges. A scalar ref points at a payload word, not a child object;
a scalar payload can *look* like an address, but the kind byte is the authority,
so scalars are never chased. When a scalar ref sits in a durable root slot, GC
copies its boxed payload (`copy_scalar_box_to_space`, a small `ScalarBox` heap
object) and rewrites the root to the copy — copied, not followed.

## Persistent Roots

Anything that outlives a scheduler or GC boundary is held as `AnyValueRef`,
because the ref is self-describing — a scalar ref has no children, a heap ref is
scanned by object layout, and sentinels have no children. The process mailbox is
`VecDeque<AnyValueRef>` (`runtime/src/process.rs`); a parked receive
(`runtime/src/park.rs`) keeps its pinned snapshot, per-clause matcher outputs,
and bound values as `Vec<AnyValueRef>`. Map construction has no process-root
builder — a map is a fold of immutable put operations.

## Policy: one value model, copy on cross-process send

There is exactly one dynamic value model. Mailbox, matcher, interpreter, and
codegen paths all carry `AnyValueRef`; no path keeps a parallel `{raw, kind}`
carrier, and any raw-payload-plus-kind storage is visibly inside a heap layout.
That single model is why a value built on one execution path reads correctly on
another.

`send` is an `any` boundary. The caller boxes a known scalar only to send it as
`any`, then calls `fz_send_ref(pid, msg_ref)`. The runtime
(`src/exec/runtime.rs send_via`) copies the value into the receiver's world
rather than sharing heap pointers across processes:

```text
self-send:                deep-copy the message into the same heap, push to own mailbox
cross-process, parked:    run the receiver's matcher on the sender's ref;
                          on a hit, deep-copy the matched bound values into the
                          receiver heap and wake it; on a miss, deep-copy the
                          whole message into the receiver mailbox
cross-process, not waiting: deep-copy the whole message into the receiver mailbox
```

There is no scalar side path inside send.
