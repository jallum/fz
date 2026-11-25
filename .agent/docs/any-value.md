# Any Values

## The Idea

Every fz value — integer, float, atom, pid, reference, list, map, tuple/struct,
closure, bitstring, binary view, resource — is handled at runtime boundaries as one opaque
word:

```text
AnyValueRef = one word that says "here is a value"
```

The word carries a 4-bit tag (what kind) and an address (where the payload is).
An int, float or reference ref points at a boxed scalar payload word; an atom
ref holds the atom id and a pid ref holds the pid in its address field, and
neither points at anything, as `[]` and `null` do. Atom and pid are the
immediate kinds; int, float and reference are the boxed scalar kinds. Heap refs
point at a heap object. A heap reference is not a separate idea — it is the
heap-object subset of `AnyValueRef`. The interpreter, REPL, JIT, and AOT paths all pass values through
this one shape, so spawn, receive, matching, and heap reads behave the same on
every path.

```text
Int ref      -> i64 payload word        Map ref      -> map object
Float ref    -> f64 payload word        List ref     -> cons cell
Pid ref      -> u64 process id          Struct ref   -> tuple/struct object
Reference ref -> u64 counter word
Atom ref     == the atom id itself
                                        Closure ref  -> closure object
                                        Bitstring/binary-view ref -> binary object
                                        Resource ref -> resource object
```

`AnyValueRef` (`runtime/src/any_value.rs`) is `#[repr(transparent)]` over a `u64`
and is opaque: callers do not pack, unpack, or dereference it by hand. The type
owns packing, projection, and the platform difference behind the word.

## The Pieces And What They Own

- **`AnyValueRef`**: the public word. Owns packing/unpacking and projection.
  `tag()` returns a `ValueKind`; `load_int`/`load_float` read the payload word a
  ref points at; `AnyValueRef::atom(id)` is the one constructor of an atom ref
  and `load_atom` reads the id back out of the address field; `AnyValueRef::pid(word)`
  is the one constructor of a pid ref (a pid is a `u32`; a wider word is
  `PidOutOfRange`) and `load_opaque_word(PID)` reads it back from the address
  field. An immediate is never built over a slot: `from_scalar_slot` rejects
  `ValueKind::ATOM` and `ValueKind::PID` with `ImmediateHasNoSlot`; `list_addr`/`map_addr`/`struct_addr`/… project heap refs to a
  cleared address (each checks the tag and errors on mismatch).
- **`ValueKind`**: the tag, one byte. `is_heap()` (List..Resource) and
  `is_scalar()` (Int/Float/Atom/Pid/Reference) classify it; `is_immediate()`
  (Atom/Pid) and `is_boxed_scalar()` (Int/Float/Reference) split the scalars by
  whether the ref word carries the value or points at a box; `is_opaque_word()` is
  the pid and reference kinds, whose one word is meaningless as an integer: a
  pid is not `1`, and `self() == 1` is false. `debug::render_opaque_word`
  prints them as Elixir does: `#PID<0.N.S>` (the pid's low 15 bits and the
  serial above them) and `#Reference<0.0.A.B>` (the counter's high and low
  halves), in `inspect/1`, `dbg/1` and inside any container.
- **`AnyValue`**: the by-value enum a host caller decodes a ref into —
  `Null`, `EmptyList`, `Int(i64)`, `Opaque(ValueKind, u64)` (a pid or a
  reference and its word), `Float(u64)`, `Atom(u32)`, `HeapRef(AnyValueRef)`.
  An int, float or reference `AnyValue` has no address; `ref_word()` panics on one because
  it needs object-local storage before it can become a ref. An atom and a pid need none:
  `ref_word()` answers `AnyValueRef::atom(id)` or `AnyValueRef::pid(word)`.
  `Heap::box_any_value_ref` allocates a scalar box for an int, float or
  reference and nothing for an atom or pid. The interpreter's
  temporary `FnRef` view materializes, before a public boundary, the node's one
  static closure for its function (`Node::static_closure`, keyed by denotation,
  arity and `FnId`) and returns its literal ref word; the object's raw storage
  address is not a ref.
- **Container object-local metadata**: each heap object stores payload words
  plus its own kind bytes (see Container Storage).
- **`Stored`** (`runtime/src/any_value.rs`): that same pair, the stored word
  and its kind, held outside a container. `Stored::of(value)` makes it and
  `Stored::value(context)` rebuilds the value. A runtime entry takes a key or
  value of any kind as its two words, so nothing boxes a number to pass it.
- **The `fz_*` runtime ABI** (`runtime/src/ir_runtime.rs`): the C entry points
  generated code calls to read, build, and project values.

## The Public Ref ABI

Generated code handles values only through these entry points. A few examples:

```text
fz_type_of(ref)                      -> tag byte
fz_ref_load_int / _float / _atom(ref)
fz_map_get_ref(process, map, key_word, key_kind)    -> ref
fz_map_count(process, map) / fz_map_to_list(process, map) / fz_map_keys(process, map) / fz_map_values(process, map)
fz_map_has_key(process, map, key_word, key_kind)    -> 0 or 1
fz_map_delete(process, map, key_word, key_kind)     -> map ref
fz_list_head_ref(list) / fz_list_tail_ref(list)
fz_struct_get_field_ref(process, struct, field_offset)
fz_value_eq_ref / fz_value_eq_widening_ref(process, a_word, a_kind, b_word, b_kind) -> 0 or 1
fz_value_cmp_ref(process, a_word, a_kind, b_word, b_kind)  -> -1, 0 or 1
fz_inspect(process, word, kind) / fz_inspect_with(process, word, kind, options)  -> binary
fz_struct_store_ref(process, struct, slot_offset, kind_offset, value_word, value_kind)
fz_closure_set_capture_ref(process, closure, index, value_word, value_kind)
fz_binary_concat(process, left, right)
fz_binary_part(process, binary, from, size)
```

**Dynamic reads return refs into existing storage, not copies.**
`fz_map_get_ref`, `fz_list_head_ref`, and
`fz_struct_get_field_ref` build a ref over the slot already living in the
container. For an int or float slot the returned ref points straight at that
payload word (`any_value_ref_from_storage`); for a heap slot it carries the
slot's heap pointer; for an atom slot it is the atom ref of the id the slot
holds, so no ref to an atom points into the container. A struct read as a map
keeps one more difference: its keys and its `__struct__` module live in no slot,
and each is an atom, so each comes back as an atom ref. `:maps.to_list`, `keys` and
`values` (`lib/maps.fz`) are the externs `fz_map_to_list`, `fz_map_keys` and
`fz_map_values`, which list the map in one walk (`Heap::map_list`): each entry's
stored word and kind are copied into a new list cell, or into the two fields of
a new `{k, v}` tuple, so nothing is decoded or boxed. `Enumerable.Map`'s
`reduce` and `reduce_while` are `List.reduce` and `List.reduce_while` over
`Map.to_list`, as Elixir's are over `:maps.to_list`, and `member?` is the match
`%{^key => ^value}`.

`fz_binary_part` is `:erlang.binary_part/3` once the bounds are checked: it
slices `size` bytes from byte `from` through `Process::slice`, so a part over
`SHARED_BIN_THRESHOLD_BYTES` is a view on the source buffer.

The map externs declare `map`, so the heap's map entry points trust that their
argument is one: `Heap::expect_map_layout`, `Heap::read_map_value` and
`Heap::map_put_slot` read the flat, trie or struct layout without testing the
tag, and a debug build asserts it. The test that a value is a map is the
language's `is_map` guard in the `lib/map.fz` and `lib/maps.fz` wrappers, which
the compiler drops where the argument is proven. `Heap::map_layout` stays the
question "is this a map?" for `fz_map_is_map`, `named_schema` and the failure
renderer. `map_put_slot` takes a map; a map literal is built through a map
destination.

`fz_binary_concat` validates byte-aligned binary inputs and builds `left <> right`
through `Heap::alloc_concatenation`, which returns the VALUE. When `left` is a
binary view that ends where its buffer's written bytes end and the buffer has spare
room for `right`, `right` is written into that room and the result is a new
view over the same buffer, longer than `left`; `left` is not copied and keeps
its own length. Otherwise a result at or below `SHARED_BIN_THRESHOLD_BYTES` (64)
is an inline `Bitstring`, and a larger one gets a new `SharedBin` with room for
as many bytes again, each side written once. A loop of `acc <> x` therefore
allocates a buffer per doubling, not one per step. `Heap::alloc_bitstring`
remains the storage choice for every other value the runtime builds; the one
other place that splits on the threshold is `Prim::ConstBitstring` lowering,
which emits a static `SharedBin` above it. `<<a :: binary, b :: binary>>` built
through `fz_bs_begin`/`fz_bs_write_field_ref`/`fz_bs_finalize` does not append: it copies
the whole result into a new buffer each time.

A construction writes each field between `fz_bs_begin` and `fz_bs_finalize` through one of two
runtime functions. `fz_bs_write_word` writes every scalar field (integer, float, utf8, utf16,
utf32) from the raw word the field already is: an integer's bits, or an f64's bits for a float.
Nothing is boxed to write it. `fz_bs_write_field_ref` writes the fields that name a heap bitstring
(binary, bits) from the value's ref.

Before a construction writes anything, it tests every segment's contract
(`src/compiler2/jobs/body/construction_contract.rs`): an `integer` takes an
integer, a `float` a number, an unsized `binary` a binary (or a bitstring of
whole units), a sized one a bitstring at least `size * unit` bits long, `bits`
a bitstring, a `utf` segment a Unicode scalar value, and a named size a
non-negative integer (16, 32 or 64 for a `float`). The test is the guard of one
dispatch row, so a term the value's type already proves folds away and a
construction of proven values compiles to the build alone (fixture `01822`).
The miss calls `Kernel.__construction_failed__/1` with each segment's
`{type tag, value, size, unit}`. It raises `%ArgumentError{}` with the message
`fz_construction_failure_message` words (`runtime/src/construction_failure.rs`),
so the Raisable analysis sees an exact `ArgumentError`. The runtime picks the
segment the BEAM reports by the BEAM's two passes: sizes, unsized binaries and
code points first, then values, lengths and units in segment order. `<>`'s
fallback clause makes the same call. The write functions therefore panic on a
value outside its segment's contract as a broken invariant, not as a user error.

`Heap::alloc_bitstring_with(byte_len, bit_len, fill)` is the allocator under
`alloc_bitstring`: it picks the storage and hands `fill` the destination bytes,
so a primitive that computes its payload writes it once, in place, with no
staging buffer. `fz_binary_copy` (`:binary.copy/2`) is its caller: `n`
repetitions land in one inline bitstring or one `SharedBin` of exactly
`n * byte_size` bytes.

Two questions still read the threshold, and they are different questions:
`Heap::slice` asks whether a VIEW is worth a stub, and native
codegen asks what to EMIT for a constant bitstring — a static `SharedBin`
symbol or a call to the inline allocator — which it must decide at compile time
with no heap to ask.

### A view names a window of a buffer through its heap's BinRef

A binary above the inline threshold is two kinds of heap object, as in OTP's
`BinView` and sub-binary split. A `BinRef` (`ValueKind::BINREF`, 16 bytes) is the
heap's one reference to a `SharedBin`: word 0 holds the `SharedBin` address and
word 8 the link of the sweep chain (`off_heap_head`, `off_heap_old_head`), with the
`StubSite` that made it in the link's low nibble. It is the only binary object
on those chains and holds the one atomic retain. A `BinView`
(`ValueKind::BINVIEW`, 24 bytes of fields in a 32-byte slot) is the value:

```text
offset  0  header: the window's length in bits, with the view's shared mark
           in BINARY_SHARED_MASK -- the word a small inline bitstring leads with
offset  8  bytes_ptr: the window's first byte
offset 16  tagged pointer to its heap's BinRef (the collector traces it)
```

Because both forms of a binary lead with the same header word, the length and the
shared mark of either are read from word 0 with no test of which form it is.

A view is a byte-aligned *window*: it may start and stop anywhere on a byte
boundary of the buffer, and the whole binary is the window at the buffer's
start spanning it. Its byte offset is derived (`bytes_ptr` less the buffer's
`bytes_ptr`). Many views of one buffer in one heap name one `BinRef`: a window
or an in-place append makes only a view; a fresh buffer makes a `BinRef` and a
view; a message copy makes the receiver its own `BinRef` and view per copied
view, retaining the buffer once. A `SharedBin` does not store a bit length: the
view's header is the only authority on its length. `BINREF_*` and `BINVIEW_*_OFFSET` in
`bits.rs` are the one statement of that layout; native codegen reads the
base with one load of `bytes_ptr` (inline bytes start at +8), and the length of a
binary it has proven one (`Prim::BinaryBitLen`, a cursor's source) with one load of
word 0, masked and shifted. `Prim::BitstringBitLen` first tests that the kind is
a bitstring or a view, and answers -1 otherwise.

`Bin::of_binary(word)` (`bits.rs`) is the one decoder of a binary's tagged word in
the runtime: it reads the length from word 0 and, from one tag bit, where the bytes
start (inline at +8, or the view's `bytes_ptr`), and only `debug_assert`s the kind.
A runtime function that reads a binary is handed a proven one -- its extern's
`binary`, `bitstring`, `binary_cursor` or `c_string` parameter, checked at the
call, or a match read the compiler emits after a kind test -- and decodes it
there. A function whose question is whether a value is a binary
(`fz_pinned_binary_segment_size`, `fz_binary_equals_literal`, the interpreter's
`read_bitstring`, the debug renderer, failure text) makes one `is_bitstring_like`
test and then calls `Bin::of_binary`. A binary's ref word is its heap object word
(`AnyValueRef::from_heap_object` packs the kind and address, and `heap_object_word`
returns that word), so a ref-word argument is decoded as it arrives. Map keys, which
store a kind beside the word, decode through `Bin::of_stored`. `bit_len`, `ptr` and
`bytes` (whole bytes only) are `Bin`'s accessors; the receive dispatch reads a
guarded binary's length with the same inline `emit_proven_binary_bit_len` body code uses.

A match that takes a binary apart does not ask for a slice at all when the
rest stays inside the compiler's own code. Its demand is `Matched` (see
`pipeline.md`), and the rest travels as a cursor: `ShapeDescr::Cursor`, two
lanes -- the source binary (a traced `ValueRef`) and the bit position the rest
starts at (a raw integer the collector never traces). `<<_c, rest :: binary>>`
yields (source, position + 8) and builds nothing; reads and clause dispatch on
the rest start at the position, and `byte_size(rest)` is (bit length of source
- position) / 8, rounded up, through the `binary_cursor` extern parameter, also
without building anything: that wire type is two words, the binary's reference word and
a bit position, so a cursor passes (source, position) and a whole binary passes
(binary, 0). A use that needs the rest as a value -- storing it, sending it,
passing it to a consumer with no cursor to offer -- makes it whole at that
point with `fz_bs_read_binary_ref`, reading it as a `bits` field because a
cursor stands for a bitstring that may end between bytes. A rest that spans its whole source is the
source, so a binary that was only measured, a cursor at position 0, comes
back as itself and builds nothing. Past position 0, any byte-aligned binary field of a shared source, whether
`<<_c, rest :: binary>>` or `<<_ :: binary-size(n), field :: binary, _ :: binary>>`,
asks `Heap::slice` for a view: another view over the same bytes
at its own offset and length instead of a copy. `Heap::slice` is the one place a binary
field is decided: the whole source is the source itself, a byte-aligned window over
`SHARED_BIN_THRESHOLD_BYTES` is a view on the source's buffer (a source that large is
always a view), and anything else is a copy, so a short slice cannot pin a long buffer.
A walk that only matches and measures allocates
no binary at all; one that makes each rest whole copies at most that short tail
per step, where a copy per step would cost n + (n-1) + … bytes.

`:binary.referenced_byte_size/1` reports the buffer a binary references.
`fz_binary_referenced_size` answers the whole `SharedBin`'s written `bytes_len`
(not its spare room) for a view whatever its offset and length, and the
binary's own size for an inline bitstring. `:binary.copy/1` makes a binary that
references only itself, which is how a program detaches a view from the large
buffer it keeps alive.

The buffer carries one invisible trailing NUL after its last byte. A window that
ends where the buffer ends (`BinView::ends_at_buffer_end`) has that NUL right
after it, so `fz_binary_as_cstring` hands it to C as it is. Any other window has
the parent's next byte there, and `fz_binary_as_cstring` copies it into a fresh
binary on the calling process's heap, which is terminated. That is the one place
a view pays for its NUL; `fz_binary_as_ptr` promises no NUL and never copies.

### Spare room belongs to one process

A `SharedBin` has a capacity and a written length (`bytes_len`). Its `room`
word holds the capacity, with a frozen flag in its top bit;
the spare room is the capacity less `bytes_len`, and zero once frozen. Buffers
that no concatenation allocated (`shared_bin_alloc`, the compiler-baked static
buffers, whose word is 0) have no room. `bytes_ptr` never moves for a live
buffer: a longer result than the room holds is a new buffer.

A heap-backed `SharedBin` is one allocation: the 48-byte header, then the
bytes, then the room, then the trailing NUL, with `bytes_ptr` pointing just past
the header. The block is allocated unwritten (`UNWRITTEN_BYTE`-filled in debug
builds) and the NUL is written at creation and after every in-place append, so
nothing beyond the NUL is read. `bytes_ptr` stays a field because a compiler-baked
static `SharedBin` keeps its bytes elsewhere in `.data`, and because a view's
offset is derived from it.

Only the process that owns a buffer appends to it. A view that ends where the
written bytes end is handed to C as a string with no copy because the byte after
it is a NUL; another process writing there would replace that NUL under a call
in progress. So every path that makes a buffer reachable from another process
closes its spare room first, on the sender's thread: `deep_copy_any_value`'s
view arm calls `shared_bin_freeze`, and every cross-process copy goes through it
(`gift_copy` for a message or a spawned closure's captured values, and the spawn
paths in `aot_shim.rs`, `ir_interp/backend.rs` and `exec/runtime.rs`). `shared_bin_freeze` writes only a buffer with spare
room; one with none, such as a compiler-baked static buffer every scheduler
thread sends views of, is only read, as OTP's `erts_pin_writable_binary`
touches only a binary that is still writable. An unfrozen buffer with spare
room has stubs on one heap only, so changing `bytes_len` has no concurrent
reader. A message copy makes one BinRef for each view it copies, as OTP's copy
makes one per copied sub-bitstring. The heap destructor frees `capacity + 1` bytes, frozen or
not.

Within one process a binary carries a shared mark (see "Shared Lists, Structs
And Binaries" below). A clear mark says the binary has one holder and, for a
view, that the view ends at its buffer's `bytes_len`: an in-place append marks
the view it grew from, and a window marks the view it was cut from. Nothing
reads the mark yet.

Copied bytes are counted. `HeapAllocStats::shared_bin` records off-heap binary
buffers, separately from `total` because they are not heap bytes and do not move
under Cheney. Without it, copying is invisible: a view costs the same whether
its bytes were freshly copied or shared, so the view counters alone cannot tell
the two apart.

**Typed writes** hand a known scalar straight into a container's compact
object-local layout, with no detour through a built scalar ref:

```text
fz_map_put(process, map, key_word, key_kind, value_word, value_kind)
fz_list_cons_int(process, head_i64, tail_word, tail_kind)
```

Compiled code calls `fz_list_cons_*` only for a tail that may not be a list: for
a list tail it writes the cell itself from
the same definition (`native_codegen/list_cell.rs`, a row of the recipe table;
see [externs](externs.md), "Inline recipes"), and the functions stay as the
definition the recipe's test compares against.

The `*_put_ref` / `Heap::alloc_list_cons_ref` paths are for already-dynamic
refs. They call `reject_scalar_ref_write` and panic on a scalar ref, so a
scalar always travels the typed-write path and the representation stays
honest.

### Walkthrough: read a value out of a map

A map holds `:answer => 42`. The 42 lives in the map's value storage. The read
hands back a ref over that slot:

```text
value_ref = fz_map_get_ref(process, map_ref, answer_atom_id, ATOM)
  value_ref.tag()      = Int
  value_ref points at  the stored i64 slot
fz_ref_load_int(value_ref) -> 42
```

If the map holds another map at `:child`, the same call returns a `Map` ref
directly — no two-part `{address, kind}` result is needed:

```text
child_ref = fz_map_get_ref(process, parent_map_ref, child_atom_id, ATOM)
  child_ref.tag() = Map  ->  child map object
```

## Generated-Code Value Lanes

Generated code keeps a value in the narrowest representation the typer can
prove. The codegen-side enum is `CodegenValue`
(`src/compiler2/native_codegen/value.rs`); the ABI-side enum threaded through
call signatures is `ArgRepr` (`src/compiler2/native_codegen/repr.rs`). The
lanes:

```text
ValueRef  // one AnyValueRef word; the only `any`-shaped lane
RawInt    // proven i64
RawF64    // proven f64
RawAtom   // proven atom id
Condition // raw i1 from a comparison/type-test whose result is only branched on
```

compiler2 picks each lane (`AbiValueRepr`) and codegen copies it with
`arg_repr_from_compiler2`: float -> `RawF64`, integer -> `RawInt`,
atom-subtype -> `RawAtom`, else `ValueRef`. `CodegenValue` adds `AnyRef` (an
`any` ref value) and `Known { payload, kind }` (a compile-time-constant scalar);
both report `ArgRepr::ValueRef`. Every lane has `abi_arity() == 1`: a value is
always one machine word across a call boundary, never split into payload + kind.

A boundary crossing allocates only for an int or float. Compiled code places
that one-word box itself with `emit_place` and stores the payload; the runtime
functions `fz_box_int_for_any` and `fz_box_float_for_any` are the definition the
recipe test compares against, the interpreter's calls, and the receive dispatch
bodies' calls (those bodies are entered from Rust, not in the pinned register). An atom has no box:
native code ors the id with the atom tag word inline (`atom_ref_word`), the
interpreter calls `AnyValueRef::atom`, and neither touches the heap.

Boxing happens only where a typed lane meets an `any` boundary.
`CodegenFn::coerce_binding_to` is the one seam:

```text
RawInt   -> ValueRef : box_int_for_any   (placed in place: native_codegen/scalar_box.rs)
RawF64   -> ValueRef : box_float_for_any (placed in place when finite)
RawAtom  -> ValueRef : box_atom_for_any (one `or` of the id with the atom tag)
Condition-> ValueRef : select true/false atom, then box
ValueRef -> RawInt/RawF64/RawAtom : unbox via the ref API
matching lanes : pass through
```

So `send(pid, 42)`, where `send` takes `any`, boxes 42 because it crosses into
`any`, then passes one `ValueRef(Int)` word. Copying the bits of a
`ValueRef(Int)` straight into a `RawInt` slot is never valid: that word is a ref,
not the integer payload. The same coercion rule covers call arguments,
continuation arguments, and typed closure capture slots.

## Tags And Platform Packing

`ValueKind` tags are semantic and platform-independent (`runtime/src/any_value.rs`):

```text
0  Null        4  Closure       7  Resource      14 Float
1  List        5  Bitstring     8  BinRef        15 Atom
2  Map         6  BinView       13 Int
3  Struct
```

`11` and `12` are unused; `ValueKind::new` rejects them. The empty list is `List` with a
null address (`AnyValueRef::empty_list`). Object storage also uses an
`EMPTY_LIST` tail sentinel (`0x8`, an address inside the OS-reserved unmapped
page 0, distinct from `nil`), but that sentinel is internal list-tail
plumbing, not the public tagged-pointer form of `[]`.

The *bits* that hold the tag are per-arch, owned by `AnyValueRefPacking`:

```text
arm64 (TBI):          tagged = address | (tag << 56)
x86_64 (canonical):   tagged = address | (tag << 57)
```

`fz_type_of` returns the same semantic tag on both, so callers never see the
difference.

An atom ref is the tag word or'd with the id, on both archs. The id names no
address, so the x86_64 clearing sequence below is never applied to it: only a
fresh stack or heap pointer needs its high bits cleared.

Compiler-emitted pointer refs follow the same split, in
`src/compiler2/native_codegen/closure.rs` and
`src/compiler2/native_codegen/fn_ctx.rs`. On arm64/TBI a fresh
stack/heap pointer is tagged by OR-ing the top-byte tag word directly, with no
address-mask clear. On x86_64 canonical refs the high bits are cleared with
`ishl_imm` then `ushr_imm` before OR-ing the tag word. Keeping codegen on
`AnyValueRefPacking` rather than a hardcoded mask is what keeps
compiler2 CLIF dumps aligned with the runtime packing model.

## The literal bit

A *literal* is an object the program carries in read-only data rather than on a
heap: a static struct (`.fz_static_struct_*`), a static closure, a halt
continuation, a short binary literal. Every reference to a literal has one bit set
above the kind field of its address word: `1 << (tag_shift + 5)`, bit 61 on
arm64 and bit 62 on x86_64, owned by `AnyValueRefPacking`
(`literal_bit`, `is_literal`, `raw_address`, `payload_mask`). The bit sits in the
*address* word, so the same position holds in the ref word, a struct field or
closure capture payload, a map key or value payload, a list head payload and a
list link's tail. `ValueKind`, kind bytes and the map key/value kind byte are
unchanged, and `AnyValueRef::tag()` ignores the bit.

A binary literal of `SHARED_BIN_THRESHOLD_BYTES` (64) or fewer is one read-only
object with a heap bitstring's layout (`bitstring_object_image`: header word,
bytes, a NUL, zero padding to 16). Native code emits one per distinct bytes and
bit length per module (`BitstringLiterals`, `.fz_bs_literal_*`); the interpreter
keeps one per node (`Node::static_bitstring`, through `binary_literal_value`).
Naming such a literal allocates nothing, a collection leaves it in place and a
message copy shares it. A longer literal is a static `SharedBin`, and naming it
allocates the view over it.

The bit is set only where a literal is named: `static_object_ref`, the entry
thunk, the child-literal payload words of a static struct (a relocation whose
addend is the bit), and an int or float field read from a literal struct
(`read_struct_field_ref`; a heap child keeps the bit its stored payload word
carries, and an atom field is its id, which names no object and carries no
bit). Fresh heap allocations never set it. Anything that dereferences,
compares identity, hashes or keys on an address reads it through
`AnyValueRefPacking::raw_address` (`AnyValue::heap_addr`, `storage_addr`,
`AnyValueRef::*_addr`), so a literal and its raw address agree; code that
re-packs an address must carry the bit (`AnyValueRef::literal`) or it names a
heap object that is not there.

The collector, deep copy and the debug formatter test this one bit: a tagged
reference is left in place (collector) or shared (deep copy), an untagged one is
a heap pointer in from-space or, for a minor collection, in an old block it
leaves as it is. The collector asks `FromSpace::moves`: untagged, and inside the
from-space. A major collection's from-space is every block, so that is the
literal bit alone; a minor collection's is the young blocks, read off the age
table: one byte per granule of the reserved heap range (`heap/arena.rs`), set
for a block allocation made and clear for every other block. A pooled span
keeps one capacity at one address for good, so its table bytes are all equal and
the first decides; a block made reads that byte and writes the span only when
the byte differs from the wanted mark. A released pooled block keeps its mark,
which is why no reader may ask the table about a freed address (the debug
classifier cannot tell a stale pointer into a free pooled block from a live
one). Exact and huge spans come from the splitting span list and write on make
and clear on release. The range and the table grow by hinted mmap at their
exact ends; an extension that lands elsewhere panics. Debug builds also record old blocks and
cross-check (`FromSpace::assert_classified`, `HeapView::assert_classified`): an
untagged pointer must lie in a young or old block (`HeapView` also asks that it
lie in the source heap's blocks), a tagged one in none, and none may lie in
to-space. `fz_frame_for_write` reads the same table through `Reservation::is_young`,
after its own literal check, because a frame can be a literal outside the range.

One `Tracer` (from-space, heap, schemas, the heap's worklist of copied objects) is
the collection's context, and `Tracer::forward(word, kind)` is its one
forwarding primitive. The pair is a stored word (address and literal bit) and
its kind. A non-heap kind, a null address and an object `moves` rejects come
back unchanged; any other object is copied once, its forwarding marker written,
and the word returned with its address bits replaced, so a word that carries a
tag above its address keeps it. A trace method reads (word, kind) from a slot
and writes the returned word back; it never builds or decodes an `AnyValue`,
and a kind is never rewritten, since forwarding never changes one.
`forward_root` is the one root entry: a boxed scalar root copies its 16-byte
box, and every other root forwards as its `AnyValueRef` word. `forward` is
`#[inline(always)]` because the trace's speed depends on it inlining into each
trace loop, and the optimizer's choice there shifts with the codegen-unit
split.

## Container Storage

Containers *appear* to store `AnyValueRef`s when dynamic code reads them, but
that is a projection rule, not the physical layout. Each object holds payload
words plus its own packed kind metadata, and the ref API reconstructs a ref on
read:

```text
List cons (16 bytes): head payload word
                      link word = tail address + head kind and alias bit in the
                                  high bits + terminator flag (bit 63);
                                  the low nibble is clear
Map:                  count, one packed key/value kind byte per entry,
                      then key payload words, then value payload words
                      -- UP TO 32 ENTRIES ARE SORTED BY KEY; more are a hash trie, see below
Closure:              ClosureDenotationId + header word, code pointer,
                      capture payload words, capture kind bytes
```

A list that ends in a value that is not a list (`[1 | 2]`) is an *improper*
list. `ListLink::tail()` answers a `ListTail`: `Proper(addr)` (0 is `[]`),
`Terminator(cell)` or `Hole`. The last cell's link carries the terminator flag
(bit 63, disjoint from the address, kind, alias and literal bits) and names a
*terminator cell*: an ordinary 16-byte cons whose head holds the terminator as
a (payload, kind) pair and whose tail is `[]`. A terminator cell is therefore an
ordinary list cell to the collector (`ListCons::tail_cell_addr` is the one edge
it follows), to deep copy and to `share_spine`; a scalar terminator is stored in
the cell and boxed nowhere. The constructors are `ListLink::to_addr` (proper
only), `to_terminator` and `hole`; `ListTail::value` is the tail as a term and
refuses a hole. A set flag with a zero address is a hole, reserved for a
destination that fills its terminator after the cell is placed; every reader
refuses it. `Heap::alloc_list_cons_any(head, tail)` places the terminator cell
for a tail that is not a list, and a cell rebuilt in place takes a whole new
link, so a rewrite drops the flag. `length` of an improper list raises
`ArgumentError` (`fz_list_length` answers -1); comparison orders the terminators
as terms after equal elements, as Erlang does, and the hash folds the
terminator in.

Every header word keeps its low nibble clear, because the low nibble belongs to
the Cheney forwarding marker (see "GC: Roots, Edges, And Lifetime" below). Little-endian:

```text
Struct:    (schema_id << 32) | named bit (bit 5) | shared mark (bit 4)
Closure:   (denotation << 32) | (flags << 4) | (arity << 20)   arity < 4096
Bitstring: bit_len << 4 | shared mark (BINARY_SHARED_MASK)
Map:       count << 4                                  (published)
           FLAG(bit 63) | filled << 33 | capacity << 4  (destination, 29-bit fields)
```

Accessors (`struct_schema_id`, `closure_denotation`, `closure_arity`,
`bitstring_bit_len`, `map_count`) and constructors (`struct_header_word`,
`closure_header_word`, `bitstring_header_word`, `map_header_word`,
`map_destination_header_word`) in `runtime/src/any_value.rs` are the only code
that knows these layouts.

The closure header separates user arity from captured count and scheduler halt
kind. A user closure has exactly one slot per lexical capture, in the immutable
source binding order fixed before specialization. Each slot retains the whole
runtime value: raw scalar payload plus kind byte, or one composite/callable
reference. Demand, inlining, and wrapper ABI choices do not erase captured
information. Invocation projects those values into the selected execution ABI;
capture reads ask the slot's kind byte and carry no construction-set lookup.
Construction wrappers retain the source type annotation beside each capture
layout. Physical callable descriptors share function, arity, and layouts only;
specialization never replaces the wrapper's capture annotations.

`ClosureDenotationId` projects the World's `FunctionId` into the header.
The Node retains the same shared typed `FunctionDenotation` source origin for
ordering. Code pointers and wrappers own execution; source denotation plus the
one immutable environment owns runtime identity. GC and transport preserve
both. Scheduler-only closures use `INTERNAL`, which user rendering and
comparison reject.

### A named struct's module is its schema identity

A struct's schema identity is `SchemaIdentity::Named(ModuleName)`, and that is
the only place its module lives: the heap object stores no module word and the
registry keeps no second copy. Three reads of that identity exist:

- `p.__struct__` answers the atom `Elixir.<Name>`, the same atom an alias
  spells in value position, so `p.__struct__ == Pt` holds. Where the types
  name the one struct `p` is, the backend step is that constant and nothing
  is read. Otherwise it lowers to `Prim::StructModule`, which calls
  `fz_struct_module`: the `__struct__` key read through the map view, so a
  struct and a map carrying that key answer alike. It is a read of the
  identity, not a stored field; `ProjectionKind::StructField` in patterns never
  names it.
- `Heap::named_schema` answers the struct schema of the module a map names.
  A value in the struct layout names its own schema. A map in the entries
  layout names the atom under its `__struct__` key: `NamedSchema::Schema` where
  a struct is registered for that module, `NamedSchema::Undeclared` where none
  is, and `NamedSchema::None` where the key is absent or holds no atom.
- The inspect renderer's `struct_value` prints by identity: a Range as its
  literal (`1..10`, `1..10//2`), a named struct as `%Name{field: value}` in
  schema order (a nested module as `%Outer.Inner{...}`), a tuple as `{a, b}`.
  A struct's fields are keyword entries: each name is spelled by the same
  keyword-key rule as a map's or a list's (`"foo bar": 1`), and each field
  spends one from the `limit:` budget (`%Pt{x: 1, ...}`). The `__exception__`
  field is not printed and spends nothing.

### A run-time type test reads the module in either layout

A `RuntimeTypePredicate` carries two answers about maps. `maps` admits the
maps that name no module. `named_structs` is the set of modules a map may
name. The test for every map (`RuntimeTypePredicate::map_kind`) sets `maps`
and admits every module.

A value of kind `STRUCT` is asked by its header. Its named bit (bit 5 of the
header word, `STRUCT_HEADER_NAMED_MASK`) says its schema is a named struct's, so
"any named struct" is one test of the word, and "a tuple" is its absence. The
bit repeats `Schema::struct_name`, is written by every constructor
(`struct_header_word` takes a `StructName` beside the schema id, and
`SchemaRegistry::struct_header` answers the runtime's own) and never changes,
so a copy or a collection keeps it; the collector asserts it agrees with the
schema table. Only a question about particular names or arities compares
schema ids. A value of kind `MAP` is asked by `Heap::named_schema`: it passes the `maps` axis where it names no
module and the `named_structs` axis where the module it names is admitted, so
a struct grown by a put of a new key still passes its struct's test. The
interpreter reads through `RuntimeValueReader::map_module`; native code calls
`fz_map_named_schema_ref` under a `MAP` kind guard and compares the word
against the admitted schema ids. Where a test admits every map or no map the
kind alone answers and nothing is read.

The emitter (`native_codegen/runtime_test.rs`) asks the axes that cost one kind
comparison first and reads further only where they have not admitted the
value, so `is_map` of a map decides on its kind: `emit_runtime_type_branch`
jumps to the caller's admit block from the first axis that admits, and a map is
admitted by the MAP comparison (`value_is_tag` compares the kind word as read,
with no byte cut out of it). A caller that needs a value takes
`emit_runtime_type_flag`, the same branch with its outcomes joined. A named struct is admitted by the
STRUCT comparison and the named bit, and no schema id is read or compared. The interpreter reads the same bit
(`struct_read` in `runtime_type_predicate.rs`).

A tuple is a `STRUCT` with an unnamed schema, so it is no map:
`Heap::map_layout` answers `None` for it, and `is_map`, a map pattern and
`fz_map_is_map` all ask `map_layout`.

### A field of a known struct is a slot

`Types::sole_struct` answers the struct every value of a type is, when there
is exactly one: the type admits only maps, and each of its clauses names the
same struct. Two field typings of one struct, or a struct with some values
subtracted, still name it.

An update that replaces `__struct__` types its result as the record holding
the new value under that key (`Descr::refine_map_field`), so the result names
the new module, or none where the value is not one atom, and its fields are
found by name.

`BackendLowerer::field_read` asks that of the receiver of every `base.field`.
A known struct's declared field becomes
`BackendStep::StructSlot { base, module, slot, field }`, with `slot` the
field's position in its `defstruct`. Any other receiver (a
map, a resource, a union of two structs, `any`) keeps
`BackendStep::FieldAccess`, which finds the field by name at run time. The
step is part of the backend program, so the interpreter, the JIT and the
native build all read by slot.

The type says which struct a value is, not how it is laid out, so the step
asks at run time. A value in the struct's own layout is read by slot. A value
in the entries layout is read by name, as `FieldAccess` reads it. The
interpreter asks `Heap::has_struct_layout_of`. Native code asks
`CodegenFn::has_struct_layout`: the reference's kind is `STRUCT` and the
object's first word is the struct's header word, both tested inline before
one branch. The read by name is the cold block.

The interpreter reads the slot with `fz_struct_get_field_ref`. Native code
lowers the step to `Prim::StructSlot`. When
the field's type is an integer, a float or an atom, `CodegenFn::load_slot`
emits the read in place: the reference word masked to its address, then one
load at `STRUCT_PAYLOAD_OFFSET + slot * 8`. The type says what the slot
holds, so the kind byte is not consulted. A field of any other type keeps the
runtime call, which reads the kind byte to build the field's reference. For
example, `p.y` on a `%Point{x: integer, y: integer}` in the struct layout is
the layout test, a mask and a load.

### A struct or tuple is one allocation, stored in place

`SlotLayout::of(fields)` is the layout of every struct and tuple: the header
word, one 8-byte slot per field, then one kind byte per field, padded to a
whole word. The runtime, the collector, static literals and compiled code all
place a field by it.

Compiled code builds one in `build_struct`. When every field is a constant
the object is read-only program data. Otherwise `CodegenFn::alloc_struct`
places the object with `emit_place` (the one inline bump) and writes its header
word itself, the schema id in the high half and the named bit (`emit_struct`,
`native_codegen/inline_object.rs`; the row is `Heap::alloc_struct_unwritten`
in the recipe table, which takes the header word and the size as constants).
The size is the layout's, a constant. The runtime is
asked only for room, when the tip is full. `CodegenFn::store_field` then
stores each field:

- A value whose kind the compiler holds (a raw integer, float or atom, a
  comparison's answer, the empty list) is two stores in place: the raw word
  at its slot and the kind at its kind byte.
- A reference whose type is a tuple, a map or a binary
  (`ty_is_addressed_object`) names its object by address, so it is also two
  stores in place: the reference without its kind, and the kind the reference
  carries.
- Any other reference may be a list or a boxed scalar. Its word and kind are
  read out of it (`list_cell::stored_parts_of_ref`) and go through
  `fz_struct_store_ref`, one call that shares the spine if the value is a
  list, and writes the word at the slot and the kind byte at the offsets it
  is handed. The interpreter's struct update calls the same entry with
  `Stored::of(value)`, so it boxes no number either.

The payload is not zeroed first. Every slot and kind byte is written before
the construction's next instruction, and the collector runs only between
quanta (`end_quantum`), so nothing reads the object half built. The bytes
after the last kind byte only pad the object to whole 16-byte slots, and
nothing reads them. The
interpreter and the runtime's own tuples use `Heap::alloc_struct`, which does
zero the payload, since their stores are not adjacent to the allocation.

### A map is a flat sorted array, or above 32 entries a hash trie

Every map has one entry per strict structural key. Up to `MAP_FLAT_MAX` (32) entries they are stored in comparator order in one array; a larger map is a trie (below).
`TermComparator` borrows Node and SchemaRegistry and is the authority for
construction, lookup, updates, equality, order, and iteration. Equal tuple,
list, nested-map, and binary keys collide even when separately allocated.
Integer and float kinds remain distinct recursively; numeric ordering compares
exact mathematical values before using kind to break strict ties. Signed float
zeros are distinct strict keys but equal under widening comparison. Equal binary
bits share identity across inline and view storage. Named schemas retain
typed module segments, and tuples use typed arity, so display collisions never
alias identities. AOT transports the same segments without a rendered-name bridge.
Resource keys retain the generative ID in their existing off-heap owner.
After validity checks, retained value identity proves equality without visiting
children; a shared immutable DAG is not expanded into a tree of comparisons.
Distinct allocations still compare by structural contents.

Public slot/ref builders normalize once: stable sort, then last-value-wins
deduplication. An unpublished destination header records capacity and filled
count, so each input entry writes its next slot directly. Freeze normalizes
and compacts that same allocation, then clears construction state. A published
map cannot be reopened for mutation. A put finds its slot with the one
ordered search (`Heap::find_or_place`); a delete and a lookup find theirs with
`Heap::find`. One writer (`Heap::write_flat_map`) makes every flat map that
comes from another: it takes the source and an `Edit`, which inserts an entry
at a slot, replaces the entry there, leaves it out, or changes nothing. The
entries kept are copied as their stored words and kind bytes, none decoded:
each was shared when it was first stored, so only a new entry is published.
An edit that keeps the count copies the map whole and stores the one entry.
A struct that leaves its schema is first written as the entries map it
spells, and the put or delete is then that map's. An absent deletion returns
the original map with no allocation. GC and
cross-heap transport preserve structural order without a sort.

A list, tuple or map literal whose every part is a constant is one `Const`
step carrying a `LiteralTerm` (`LiteralTerm::constant`,
`src/literal_term.rs`): its parts are not steps, and its type is computed from
the term by the rules the tuple, list and map steps use. Native code builds it
with `literal_var` and the interpreter with `literal_term_value`; a constant
tuple whose layout spreads its fields over lanes is encoded field by field
(`literal_bound`). A constant list or map is still built on the heap each time
it is evaluated, and a constant map with atom keys is written in key order
(`LiteralTerm::entries_in_key_order`) and published without a sort.

A map literal whose keys are all literal atoms is sorted by the compiler, not
the runtime. Atoms order by name, so `entries_in_key_order`
(`src/compiler2/jobs/backend.rs`) writes `BackendStep::Map`'s entries in key
order, keeping the last entry written for a repeated key, and marks the step
`in_key_order`. Every value is its own earlier step, so each is still
evaluated, in source order. Such a literal fills its destination in order and
ends in `Prim::DestMapPublish` (`Heap::map_destination_publish`), which
publishes the entries where they stand; a debug build asserts the order. For
example, `%{b: f(), a: g(), b: h()}` calls `f`, `g` and `h` in that order and
puts `a` then `b`, with `h`'s value. A literal with any other key keeps its
source order and ends in the freeze. A flat build destination is sorted where
it stands (`Heap::normalize_destination_entries`): entries move as the tag
byte and key and value words they are stored as, and only keys are decoded,
to be compared. A repeated key keeps its first slot and its last value, and
the survivors move down to the layout of the smaller count
(`compact_destination_entries`) before they are published in place. A
destination of more than `MAP_FLAT_MAX` entries is published as a trie from
its normalized entries. The interpreter and native code build every map
literal this way.

A single update of a flat map copies the array of at most 32 entries; an update
of a trie copies one path (below). Use bulk operations when touching several
keys. Iteration of a flat map
follows strict fz term order, including atom names and binary content;
Elixir's atom-key iteration may differ because it uses VM identity.

#### The hash trie above 32 entries

`term_hash` (`runtime/src/term_hash.rs`) is the one hash, and it agrees with
strict key equality: equal keys hash equal in every representation. Ints and
floats hash under different tags, a float by its bits; a bitstring by bit
length and content, whether inline or a view, with the bits
past its length left out; a tuple by arity and fields; a map as a sum over its
entries, so a flat map, a trie and a named struct spelling the same entries
hash alike; a pid, ref or resource by its word. An atom hashes by its key
hash (`atom_key_hash`, a hash of its name), which `AtomTable` keeps when it
interns the atom, and a closure by the hash of its source denotation, which the
`Node` keeps when it registers the denotation. Neither depends on an id, so trie order is the same under the
interpreter, `run` and `build`. A hash walks a tree of containers, so after 256
containers it remembers each container's hash by address and a shared
substructure costs one lookup.

A trie node (`runtime/src/any_value/map_node.rs`) is a Map object whose first
word has bit 62 set:

```text
trie node:   TRIE | total << 36 | child_map << 20 | data_map << 4
collision:   TRIE | COLLISION | count << 36
node body:   tag bytes, keys, values (one per data_map bit), children (one word per child_map bit)
```

The node size is a function of its header alone, and the low nibble stays
clear for the forwarding marker. A hash takes four bits per level, top bits
first, sixteen levels; a slot holds an entry or a child, and a node exists
only where two or more keys share the path, so a key set has one trie whatever
order built it. Keys with equal 64-bit hashes share a collision node and are
told apart by equality. `total` counts the entries at and beneath a node, so
the root answers `map_size` in constant time and bounds a map at 2^25 entries.
The collector traces a node's own entries and its children from the header, and
deep copy and gift copy each node once per path that reaches it.

The child map lies right above the data map and the bits below the data map
are clear, so where an entry or a child sits is one left shift of the header
and a popcount: shifted by `60 - slot`, the header keeps the data bits below the
slot; by `44 - slot`, the child bits below the slot and every data bit, which is
the child word's distance from the first value. Compiled code walks a trie this
way (`WordKeyFind`, in `docs/pattern-matching.md`), and reads an atom's key hash
through `Process::atom_key_hashes`: the address of the table's word that holds
where the key hashes begin, which the table updates as it grows and which
stays where it is while the node lives.

`Heap::map_layout` answers `MapLayout::Trie` for a root. A map of more than 32
entries is always a trie and a map of 32 or fewer is always a flat array:
`alloc_map_slots`, `alloc_map_refs_bits`, `fz_map_from_kv` and the destination
freeze and publish make a trie when more than 32 entries result, a put of a new
key on a flat map of 32 entries makes one (`map_put_entry`), and a delete on a
trie of 33 entries makes the flat array (`trie_delete`). Debug builds assert
that no flat map is published with more than 32 entries.

Put and delete on a trie (`trie_put`, `trie_delete` in
`runtime/src/heap/map_trie.rs`) copy the nodes on the path from the root to the
slot the key's hash names, and share every other node by pointer. A put
replaces the value of an equal key, fills an empty slot with an inline entry,
or, where the slot holds another key's entry, moves both into a new child
(repeating a level while their hash bits agree, and ending in a collision node
when all sixteen levels agree). Each copied node's `total` is updated. A delete
that leaves a child holding one entry pulls that entry up into its parent, so
a key set has one trie whichever puts and deletes built it; a collision node
keeps its entries in key order for the same reason. Deleting an absent key
returns the map it was given and allocates nothing. Nodes are allocated
bottom-up and each is complete before the next allocation; allocation never
collects (collection runs between quanta), and no old node is written. An
update `%{m | k: v}` of a trie uses the trie as its own destination:
`alloc_map_update` answers the root, each put of an existing key is a
`trie_put`, a put of an absent key is the miss, and freeze answers the trie.
Enumeration (`map_view_entries`, `Enum`, `Map.to_list`, `for`,
`inspect`) is node order: a node's entries in slot order, then each child's. It
is a function of the hashes, so anything that needs key order sorts the entries. Entry `i` of a trie (`map_view_entry`) skips
whole children by their totals and costs one header read per child passed, so
reading every entry by index costs more than one walk; `Map.to_list`, `keys`
and `values` walk once (`Heap::map_list`). Equality and ordering of two maps are those of the
same entries in a flat map: ordering sorts both sides by key.

### A struct is a map in its own layout

A named struct is a map whose keys are its fields and `__struct__`. It has a
second physical layout, the schema-backed object, but no operation asks which
layout it holds: every map read and write goes through
`Heap::map_layout` (`runtime/src/heap/map_view.rs`), which answers
`MapLayout::Entries` for the sorted array, `MapLayout::Trie` for a trie root and `MapLayout::Struct` for a named
struct, and `None` for every other value, a tuple included. A struct's keys
come in map key order, `__struct__` among them; `SchemaRegistry::map_keys`
holds that order once per schema.

Comparison and printing read the map, not the layout.
`TermComparator` (`runtime/src/term.rs`) places a named struct in the map
category of the term order, after every tuple, and compares two maps by size,
then keys, then values in key order, reading either layout through
`MapTerm`. So `%Pt{x: 1, y: 2} == Map.put(%{x: 1, y: 2}, :__struct__, Pt)`,
each finds the other as a map key, a pin of one matches the other, and two
structs of one size and key set differ first by the module under
`__struct__`, the least of their keys. A struct's fields are compared in key
order whatever order it declares them in. Two structs of one schema share
size, keys and module, so only their fields are read.

A map prints as `%Name{...}` exactly when it holds what the struct it names
declares. A value in the struct layout always does. A map in the entries
layout does when `Heap::entries_spelling_a_struct` answers: its `__struct__`
names a registered schema and its keys are that schema's fields and nothing
else. Its fields print in declaration order. A `Range` prints as its literal
in either layout (`1..3`, `1..9//2`): `named_struct` is the one printer of a
named struct and writes a range that way. The schema is registered for each module
the program's types name, each module whose atom a body writes, and, where
the program makes an atom from text (`String.to_atom`), every module a value
can name, so a map given its module while the program runs prints as its
struct too. Any other map naming a module
prints as a map, `__struct__` among its keys: `Map.delete(p, :y)` is
`%{__struct__: Pt, x: 1}`.

Writes keep the struct layout while the key set stays the schema's.
`Map.put` of a field copies the object with that field replaced. A key outside
the schema, or a deletion, changes the key set, so the answer is published in
the entries layout with `__struct__` an ordinary key, exactly the map Elixir
makes (`Map.delete(p, :x)` is `%{__struct__: Pt, y: 2}`).

`%{m | k: v}` uses an update destination (`Heap::alloc_map_update`): an
unpublished copy of `m` in `m`'s own layout, whose puts may only replace what
it holds. The destination is threaded through its puts.
`Heap::map_destination_put` stores one entry and answers the destination the
next put or the freeze continues with, and `Prim::DestMapPut` is that value in
the IR, so the puts of one update form a chain and nothing else holds the
destination.

- An entries base is copied slot for slot. A put finds its key by the map's
  binary search and replaces the value, so the copy stays in key order and
  freeze publishes it in place, with no sort.
- A struct base is copied by `Heap::copy_struct`. A put of a field stores it
  in the copy's slot, and freeze answers the copy, so updating a struct keeps
  it one. `__struct__` lives in no slot: a put of the struct's own module
  changes nothing, and a put of any other module moves the copy's entries to
  an entries destination that holds the new module as an ordinary key.
- A put naming a key the base lacks has no destination to continue with and
  answers `0`. Every later put passes `0` on, and freeze answers `None`, which
  `fz_map_dest_freeze` returns as the null ref, the same miss sentinel a map
  pattern's lookup answers.

Where the types say which struct the base is (`Types::sole_struct`) and every
key is a literal atom naming one of its fields, the update needs no
destination when the base is in the struct's own layout. It is
`BackendStep::StructUpdate { base, module, arity, stores, rewrite }`, which
cannot miss. It picks the object to store into, then `CodegenFn::store_field`
stores each replaced slot in place, the same stores a construction uses. The
object is the base itself when `rewrite` is `Rewrite` and the base's header
says it is not shared (see "Shared Lists, Structs And Binaries"); the update is then the
stores alone. Otherwise `fz_struct_copy` copies the base. For example,
`%{p | y: 5}` with `p` a `Point` of fields `x` and `y` is one store at slot 1
when nothing else holds `p`, and one copy and that store when something may.
Native code makes the choice inline; the interpreter calls
`fz_struct_reuse_or_copy`. The step asks the layout question a slot read asks.
A base in the entries layout takes the update destination, each store's key
put with its value.

Published language values are finite immutable DAGs. Low-level struct and closure
writes are unsafe construction operations whose caller must own the unpublished
object exclusively and supply published values with no path back. Map destinations
accept finite terms without back-edges and publish their fields when frozen.
Proper lists admit only a list tail or `[]`; collector tests may deliberately
construct cycles, but never publish them to term comparison. The comparator
allocates no visited set, temporary Process, schema copies, or scalar boxes.
Checked float construction, ref decoding, and scalar-box ingress reject
nonfinite payloads before publication. Unfinished maps, internal absence
(`NULL`), forged nonfinite float payloads, and unregistered atoms also have no
language comparison semantics and are rejected at comparator entry.

## Shared Lists, Structs And Binaries

A list cell or a struct may be rewritten in place only when two answers agree.
The compiler's answer is a `RewritePermission` on the construction:
`can_rewrite` (src/compiler2/jobs/body.rs) grants `Rewrite` when nothing the
construction stores holds the source, and nothing that can run after it uses
the source. A map update's key check does not count: it reads the base only
on the miss arm, where the update wrote nothing, and its verdict `ok` is an
atom. The runtime's answer is a shared mark on the object: set, it means
something outside the body may hold the object, which is then never written
again.

The list link's **alias bit** protects a closed shared spine: a marked cell has
a marked tail. `ListCons::share_spine` stops at the first marked cell, so repeated
publication visits only newly protected cells plus one check per Share edge.
The bit setter and link are private; shared cells cannot relink, and GC relocates
the same logical tail without changing this invariant. A collection marks every
cell it keeps (`ListCons::keep_across_collection`, from `Tracer::trace_list`), and
a gift copy marks every cell it writes (`link_list_tail`), so a cell in an old
block (one a collection kept) or in a message is never rewritten in place
and never comes to point at a value allocated after it. A minor collection relies
on this: it does not trace through old blocks.

`ListRetention { source, permission }` belongs to the exact list construction.
Identical raw head, kind, and tail retain the source even when shared or when
permission is `RetainOnly`. Changed contents require both `Rewrite` permission
and a clear alias bit; otherwise construction allocates. Physical source pointers
are traced roots, not independent semantic owners. Calls and structural tuple
fields mark actual `Share` operands before splitting ownership; `Transfer`
operands and one-shot continuation captures do not blanket-publish cells.

Materialized language containers publish their list fields at construction:
list-valued heads, tuple/named-struct fields, closure captures, and map keys/values.
Map allocation, put, and freeze share `write_ordered_map_entries`; deep-copy maps
use that same boundary. Raw `write_field_slot` remains an unpublished storage
operation used by internal runtime structs too; the language constructor, not
every internal field write, owns publication. No structural runtime scan is added.

Cross-process send copies into storage the receiver will own: the sender
copies into a gift window on its own heap (`sched::gift_copy`), and the receiver
holds the segment in its mailbox until a receive takes the message, and
grafts it then. Every list cell and struct the copy
writes is shared from birth, so a message's cells are never
rewritten in place; copied container fields protect
receiver-side sharing the same way. A copy keeps no record of what it has copied,
as a send in BEAM does not, so a subterm reached twice arrives as two copies
and nothing in a gift is aliased within it. The sender's own cells are not marked merely
because a copy was sent. Self-send copies the message into a gift on the sender's own
heap, as a send to another process does, and the segment waits in the sender's
mailbox (`sched::self_send`), so the mailbox holds no reference to anything the
sender holds. The alias bit remains one-way within a heap.

A struct's shared mark is bit 4 of its header word
(`STRUCT_HEADER_SHARED_MASK`) and its named bit is bit 5
(`STRUCT_HEADER_NAMED_MASK`). The schema id sits in the high 32 bits
(`STRUCT_HEADER_SCHEMA_SHIFT`) and the low nibble is the forwarding marker, so
neither a schema read nor the collector notices the mark. `Heap::share` is the
one setter for both kinds: a list marks its spine, a struct its header. Native
code writes the same share where it stands (`CodegenFn::share`), shaped by
what the compiler knows of the value: nothing for a type whose values are
numbers or atoms, a test and a store of the mark for a struct, tuple or
binary, a test of a list's first cell before the runtime walks its spine
(`fz_share_list_spine`), and a branch on the reference's kind when the type
does not say (`share_class` decides). An object already marked is only read,
since it may be read-only program data. A share is reached wherever a struct
can gain a second holder:

- a call argument or tuple field passed `Share` (`Prim::Share` natively,
  `publish_backend_capture` in the interpreter);
- a closure capture, including the mid-flight continuation a reduction yield
  builds (`store_closure_capture_ref_word`);
- a store into a container: a struct or tuple field, a list head, a map key
  or value (`publish_contained_parts`; natively `CodegenFn::stored_form`,
  shaped by the stored value's type as a call argument's share is, and the
  list cell a cons places);
- a collection that keeps it (`Tracer::trace_struct`), since a kept struct is
  old;
- a gift copy (`deep_copy_strict_struct`).

A struct literal native code places in read-only program data
(`define_static_struct_literal`) carries the mark from birth, so it is only
ever read. Marking the struct alone is enough: everything it holds was marked
when it was stored. An unshared struct is therefore young, which
`fz_struct_reuse_or_copy` asserts. A struct update that stores into its
base is a hit at its reuse site and one that copies is a miss, reported by
`fz.runtime.reuse_site` (see [runtime-telemetry](runtime-telemetry.md#fzruntimereuse_site)).
Native code bumps the hit inline, at the site's own counter.

A binary's shared mark is `BINARY_SHARED_MASK`, the list link's alias bit,
in word 0 of both forms: a small bitstring's header and a view's header, whose
length then reads through `BITSTRING_HEADER_LEN_MASK`. A view's `BinRef` word
(`BinView::binref_word`, offset 16) carries no mark, so the collector and a deep
copy rewrite it freely. The mark is set once and never
cleared (`share_bitstring`, `BinView::share`), and `Heap::share` and
`publish_contained_parts` reach a binary at the same publish points as a
struct, and native code marks it in place as it does a struct. A view is born by
its `StubSite`: a filled or grown buffer and an in-place append are born
clear; a window of a buffer, a message copy and a static literal are born
shared (`StubSite::born_shared`). A small bitstring is born clear, a message
copy of one included, since the copy is the receiver's own; a literal image is
born shared. `fz_bs_read_binary_ref` returning its whole source marks it, as
the source then has two names. A reduction yield in native code marks the
yielding function's arguments when it builds their continuation; the
interpreter keeps its frame across the yield and marks nothing. The process
counts each binary it marks in `binaries_shared`, reported on
`process_exited`; native code adds to it inline at
`PROCESS_BINARIES_SHARED_OFFSET`.

## GC: Roots, Edges, And Lifetime

The process heap is a moving, generational Cheney collector
(`runtime/src/heap/gc/`). The copy keeps no per-object counter: once the scan
finishes, `copied_bytes` is the fill of to-space (the fresh tip plus the blocks the
copy parked, `Heap::young_bytes`) and `copied_objects` is the worklist length plus
the scalar boxes the roots copied. Blocks have an age: the tip and the blocks allocation
has parked since the last collection, and the blocks a graft brought, are young;
blocks a collection filled with survivors are old. A minor collection copies the
reachable objects of the young blocks into fresh blocks, which become old, and
leaves old objects where they are; a major collection copies every reachable
object (`Heap::next_generation` chooses). Nothing old points at anything young:
data is immutable, and a list cell in an old block is shared, so none is
rewritten in place. An
`AnyValueRef` can point into it, so a bare ref is a *temporary*: it must not
`AnyValueRef` can point into it, so a bare ref is a *temporary*: it must not
survive an allocation, a yield, a GC, or any runtime call that may allocate or
yield, unless it has been stored in a traced root.

GC copies each reachable object as a whole unit, then follows only the payload
slots whose object-local kind byte says `is_heap()`
(`Tracer::trace_list`/`_map`/`_struct`/`_closure`/`_binview`; a resource stub holds
no heap edge):

```text
copy:   every reachable object moves as a unit
follow: only heap-shaped payload words become child roots
```

Heap-object refs (`Map, List, Struct, Closure, Bitstring, BinView, BinRef, Resource`)
are followed as edges. An int, float or reference ref points at a payload word, not a child
object; a scalar payload can *look* like an address, but the kind byte is the
authority, so scalars are never chased. When an int, float or reference ref sits in a
durable root slot, GC copies its boxed payload (`Tracer::forward_root`, a
small `ScalarBox` heap object) and rewrites the root to the copy — copied, not
followed. An atom or pid ref has no payload to copy: GC and deep copy leave it as it is,
like `null`, and a measuring pass charges it nothing. Generated code packs and
reads a pid ref inline (`immediate_ref_word`, `address_field`); a
reference is boxed in place by compiled code (the `fz_box_opaque_for_any` row)
and read through `fz_unbox_opaque`.

Off-heap binaries and resources have their own atomic reference counts. A
16-byte `BinRef` owns one edge to a `SharedBin`, and a binary view names its
heap's `BinRef` without owning an edge; a resource stub owns one edge to a
`Resource`. Both off-heap objects are 16-ALIGNED, the same invariant the process
heap keeps, and for the same reason: a stub or view holds the address in word 0,
and word 0 is where Cheney writes a forwarding marker — a pointer with a set low
nibble. At 8-byte alignment half of those addresses have a set nibble and a live
object would read as forwarded, so the sweep would write into the object it is
releasing. Alignment is what keeps a live pointer and a marker
distinguishable by construction.

The marker is the only use of the low nibble. Each kind names one marker word —
word 1 of a list cons, word 0 of every other kind — whose live value has a clear
low nibble, so "low nibble set" is the whole forwarding test: one read, no
confirming word (`runtime/src/heap/gc/forwarding.rs`). Copying a view into another heap makes that heap its own `BinRef`, which retains
one edge. Cheney copies a live view and traces its `BinRef`, copied and forwarded
once; moving a `BinRef` during GC preserves its edge; sweeping an unreachable `BinRef` or resource stub
or dropping its heap releases it. An immediate last release of a `SharedBin`
invokes the allocation's destructor and reclaims its storage. A `Resource`
holds its destructor as the value-ref word of a literal (capture-free) closure,
which lives outside every heap; deferred resource release reclaims the wrapper
and returns `(destructor, payload)` for later destructor dispatch. The 16-byte
resource stub is `shared_ptr` and `off_heap_next` alone. A deep copy of a stub
retains the shared `Resource` and copies no closure. Static binaries keep a
permanent anchor and use a no-op destructor.

Lifetime tests observe these exact allocations. A retained handle keeps the
pointer valid while checking which heap-owned edges remain. Separate scoped
destructor observations prove actual final release, including GC, cross-heap
sharing and cross-thread release. A retained witness alone does not prove
destruction, and allocations made by another test do not enter either proof.

## Persistent Roots

Anything that outlives a scheduler or GC boundary is held as `AnyValueRef`,
because the ref is self-describing — a scalar ref has no children, a heap ref is
scanned by object layout, and sentinels have no children. The process mailbox is
a `Mailbox` (`runtime/src/mailbox.rs`), which is no root: every message waits in its
gift segment outside the heap; a parked receive
(`runtime/src/park.rs`) keeps its pinned inputs, per-outcome matcher outputs,
and semantic/physical arguments as `Vec<AnyValueRef>`. Map construction carries its unpublished
heap destination through the same value representation.

## Policy: one value model, copy on cross-process send

There is exactly one dynamic value model. Mailbox, matcher, interpreter, and
codegen paths all carry `AnyValueRef`; no path keeps a parallel `{raw, kind}`
carrier, and any raw-payload-plus-kind storage is visibly inside a heap layout.
That single model is why a value built on one execution path reads correctly on
another.

`send` is an `any` boundary. The caller boxes a known scalar only to send it as
`any`, then calls `fz_send_ref(pid, msg_ref)`. The runtime
(`src/exec/runtime.rs send_via`) never shares heap pointers across processes:
the sender copies what the receiver will keep into a gift window on its own heap
and queues the segment on the receiver's `in_queue`; the receiver moves a message
and its segment into its mailbox at its next dispatch and grafts the segment when
a receive takes the message (see [scheduler](scheduler-zero-arg-closures.md)):

```text
self-send:                copy the message into a gift; it waits in the sender's own mailbox
cross-process, parked:    run the receiver's matcher on the sender's ref;
                          on a hit, gift the clause's roots (nothing when the clause
                          reads none) and wake the receiver; on a miss, gift the
                          whole message, which joins the receiver's mailbox when
                          it drains its in-queue
cross-process, not waiting: gift the whole message; it joins the receiver's
                          mailbox when it drains its in-queue
```

There is no scalar side path inside send.
