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
  scalar needs object-local storage before it can become a ref. The interpreter's
  temporary `FnRef` view materializes a closure before a public boundary and
  returns its tagged ref word; the heap object's raw storage address is not a ref.
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
fz_map_count(process, map) / fz_map_entry_key(process, map, i) / fz_map_entry_value(process, map, i)
fz_map_has_key(process, map, key)    -> 0 or 1
fz_list_head_ref(list) / fz_list_tail_ref(list)
fz_struct_get_field_ref(process, struct, field_offset)
fz_binary_concat(process, left, right)
```

**Dynamic reads return refs into existing storage, not copies.**
`fz_map_get_ref`, `fz_map_entry_key`/`_value`, `fz_list_head_ref`, and
`fz_struct_get_field_ref` build a ref over the slot already living in the
container. For a scalar slot the returned ref points straight at that payload
word (`any_value_ref_from_storage`); for a heap slot it carries the slot's
heap pointer. A struct read as a map is the one exception: its keys and its
`__struct__` module live in no slot, so those come back boxed. `Enumerable.Map` (`lib/map.fz`) is plain
fz source that declares `fz_map_count`, `fz_map_entry_key`, `fz_map_entry_value`
as externs and folds over the map's canonical sorted entries; the tuple/list it
builds copies those values into fresh containers before publishing them.

`fz_binary_concat` validates byte-aligned binary inputs and copies their bytes
into the caller process heap through `Heap::alloc_bitstring`, which returns the
VALUE — `ProcBin` past `SHARED_BIN_THRESHOLD_BYTES` (64), `Bitstring` below it.
The storage choice for every value the runtime builds is made there; the one
other place that splits on the threshold is `Prim::ConstBitstring` lowering,
which emits a static `SharedBin` above it.

Two questions still read the threshold, and they are different questions:
`alloc_bitstring_suffix` asks whether a VIEW is worth a stub, and native
codegen asks what to EMIT for a constant bitstring — a static `SharedBin`
symbol or a call to the inline allocator — which it must decide at compile time
with no heap to ask.

### A ProcBin names a suffix

A `ProcBin` stub is not "the shared binary"; it is a byte-aligned *suffix* of
one. It carries a `byte_offset`, and its length is the parent buffer's length
minus that offset. The whole binary is the suffix at offset 0. Several stubs
over the same `SharedBin` at different offsets are the normal case, each owning
its own reference edge.

That is what makes matching a tail free. `<<_c, rest :: binary>>` asks for a
suffix, so `fz_bs_read_field_bits` hands back another view of the same bytes
instead of copying them; `Heap::alloc_bitstring_suffix` decides whether the view
is worth a stub, copying suffixes at or below `SHARED_BIN_THRESHOLD_BYTES` so a
short tail cannot pin a long buffer. Scanning n bytes copies at most that short
tail per step, where a copy per step would cost n + (n-1) + … bytes.

Suffix — rather than an arbitrary window — is load-bearing. The buffer carries
one invisible trailing NUL, so a suffix ends where the NUL is and
`fz_binary_as_cstring` can hand a tail straight to C. An arbitrary window could
not, which is why one cannot be built: `alloc_procbin` derives the length from
the offset rather than accepting one.

Copied bytes are counted. `HeapAllocStats::shared_bin` records off-heap binary
buffers, separately from `total` because they are not heap bytes and do not move
under Cheney. Without it, copying is invisible: a stub costs the same whether
its bytes were freshly copied or shared, so the stub counters alone cannot tell
the two apart.

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
continuation arguments, and typed closure capture slots.

## Tags And Platform Packing

`ValueKind` tags are semantic and platform-independent (`runtime/src/any_value.rs`):

```text
0  Null        4  Closure       7  Resource      14 Float
1  List        5  Bitstring     13 Int           15 Atom
2  Map          6  ProcBin
3  Struct
```

`8`–`12` are unused; `ValueKind::new` rejects them. (`TAG_LAZY_CONT`, also
`8`, is a ref-word field code for a stack-resident lazy continuation, never a
`ValueKind`.) The empty list is `List` with a
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
continuation, and the nil slot. Every reference to a literal has one bit set
above the kind field of its address word: `1 << (tag_shift + 5)`, bit 61 on
arm64 and bit 62 on x86_64, owned by `AnyValueRefPacking`
(`literal_bit`, `is_literal`, `raw_address`, `payload_mask`). The bit sits in the
*address* word, so the same position holds in the ref word, a struct field or
closure capture payload, a map key or value payload, a list head payload and a
list link's tail. `ValueKind`, kind bytes and the map key/value kind byte are
unchanged, and `AnyValueRef::tag()` ignores the bit.

The bit is set only where a literal is named: `static_object_ref`, the entry
thunk, the child-literal payload words of a static struct (a relocation whose
addend is the bit), `nil_atom_ref`, and a scalar field read from a literal
struct (`read_struct_field_ref`; a heap child keeps the bit its stored payload
word carries). Fresh heap allocations never set it. Anything that dereferences,
compares identity, hashes or keys on an address reads it through
`AnyValueRefPacking::raw_address` (`AnyValue::heap_addr`, `storage_addr`,
`AnyValueRef::*_addr`), so a literal and its raw address agree; code that
re-packs an address must carry the bit (`AnyValueRef::literal`) or it names a
heap object that is not there.

The collector, deep copy and the debug formatter test this one bit: a tagged
reference is left in place (collector) or shared (deep copy), an untagged one is
a heap pointer in from-space. Debug builds keep the from-space range walk as a
cross-check (`FromSpace::assert_classified`, `HeapView::assert_classified`): an
untagged pointer must lie in from-space, a tagged one must not, and none may lie
in to-space. Release builds never walk the from-space ranges.

## Container Storage

Containers *appear* to store `AnyValueRef`s when dynamic code reads them, but
that is a projection rule, not the physical layout. Each object holds payload
words plus its own packed kind metadata, and the ref API reconstructs a ref on
read:

```text
List cons (16 bytes): head payload word
                      link word = tail address + head kind and alias bit in the
                                  high bits; the low nibble is clear
Map:                  count, one packed key/value kind byte per entry,
                      then key payload words, then value payload words
                      -- ENTRIES ARE SORTED BY KEY, see below
Closure:              ClosureDenotationId + header word, code pointer,
                      capture payload words, capture kind bytes
```

Every header word keeps its low nibble clear, because the low nibble belongs to
the Cheney forwarding marker (see "GC: Roots, Edges, And Lifetime" below). Little-endian:

```text
Struct:    schema_id << 32
Closure:   (denotation << 32) | (flags << 4) | (arity << 20)   arity < 4096
Bitstring: bit_len << 4
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

### The schema registry starts with the bitstring reader's tuples

`SchemaRegistry::new()` registers the arity-1 tuple (the reader's miss result)
and the arity-3 tuple (the reader state) first, at the fixed ids
`BITSTRING_RESULT_SCHEMA` (0) and `BITSTRING_READER_SCHEMA` (1). The runtime's
reader primitives allocate them by those ids, and codegen, the interpreter and
the native build's process all construct their registry with that one
constructor, so no program has to be scanned for bitstring use. Registration is
by identity, so a program's own 1- or 3-tuple resolves to the same ids. Every
other schema id follows these two.

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
- `Types::field_lookup` answers `__struct__` on a struct-tagged map signature
  with the singleton atom of that module.
- The inspect renderer's `struct_value` prints by identity: a Range as its
  literal (`1..10`, `1..10//2`), a named struct as `%Name{field: value}` in
  schema order (a nested module as `%Outer.Inner{...}`), a tuple as `{a, b}`.
  A struct's fields are keyword entries: each name is spelled by the same
  keyword-key rule as a map's or a list's (`"foo bar": 1`), and each field
  spends one from the `limit:` budget (`%Pt{x: 1, ...}`).

### A field of a known struct is a slot

`Types::sole_struct` answers the struct every value of a type is, when there
is exactly one: the type admits only maps, and each of its clauses names the
same struct. Two field typings of one struct, or a struct with some values
subtracted, still name it.

An update that replaces `__struct__` types its result as a plain map holding
that key (`Descr::refine_map_field`), so the result names no struct and its
fields are found by name.

`BackendLowerer::field_read` asks that of the receiver of every `base.field`.
A known struct's declared field becomes `BackendStep::StructSlot { base, slot }`,
with `slot` the field's position in its `defstruct`. Any other receiver (a
map, a resource, a union of two structs, `any`) keeps
`BackendStep::FieldAccess`, which finds the field by name at run time. The
step is part of the backend program, so the interpreter, the JIT and the
native build all read by slot.

The interpreter reads the slot with `fz_struct_get_field_ref`. Native code
lowers the step to `Prim::TupleField`, the slot read tuples already use. When
the field's type is an integer, a float or an atom, `CodegenFn::load_slot`
emits the read in place: the reference word masked to its address, then one
load at `STRUCT_PAYLOAD_OFFSET + slot * 8`. The type says what the slot
holds, so the kind byte is not consulted. A field of any other type keeps the
runtime call, which reads the kind byte to build the field's reference. For
example, `p.y` on a `%Point{x: integer, y: integer}` is a mask and a load.

### A struct or tuple is one allocation, stored in place

`SlotLayout::of(fields)` is the layout of every struct and tuple: the header
word, one 8-byte slot per field, then one kind byte per field, padded to a
whole word. The runtime, the collector, static literals and compiled code all
place a field by it.

Compiled code builds one in `build_struct`. When every field is a constant
the object is read-only program data. Otherwise `CodegenFn::alloc_struct`
calls `fz_alloc_struct` with the schema and the layout's size, both constants,
and gets back an object with only its header written. `CodegenFn::store_field`
then stores each field:

- A value whose kind the compiler holds (a raw integer, float or atom, a
  comparison's answer, the empty list) is two stores in place: the raw word
  at its slot and the kind at its kind byte.
- A reference whose type is a tuple, a map or a binary
  (`ty_is_addressed_object`) names its object by address, so it is also two
  stores in place: the reference without its kind, and the kind the reference
  carries.
- Any other reference may be a list or a boxed scalar. It goes through
  `fz_struct_store_ref`, one call that reads the reference, shares the spine
  if it is a list, and writes the slot and kind byte at the offsets it is
  handed.

The payload is not zeroed first. Every slot and kind byte is written before
the construction's next instruction, and the collector runs only between
quanta (`end_quantum`), so nothing reads the object half built. The
interpreter and the runtime's own tuples use `Heap::alloc_struct`, which does
zero the payload, since their stores are not adjacent to the allocation.

### A map is a flat sorted array

Every map has one entry per strict structural key, stored in comparator order.
`TermComparator` borrows Node and SchemaRegistry and is the authority for
construction, lookup, updates, equality, order, and iteration. Equal tuple,
list, nested-map, and binary keys collide even when separately allocated.
Integer and float kinds remain distinct recursively; numeric ordering compares
exact mathematical values before using kind to break strict ties. Signed float
zeros are distinct strict keys but equal under widening comparison. Equal binary
bits share identity across inline and ProcBin storage. Named schemas retain
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
map cannot be reopened for mutation. `put`, `delete`, and lookup share one
binary search; put/delete preserve order while copying the new sequence, and
an absent deletion returns the original map with no allocation. GC and
cross-heap transport preserve structural order without a sort.

A single update copies the flat array, so repeated updates remain quadratic.
Use bulk operations when touching several keys. Iteration follows strict fz
term order, including atom names and binary content; Elixir's atom-key
iteration may differ because it uses VM identity.

### A struct is a map in its own layout

A named struct is a map whose keys are its fields and `__struct__`. It has a
second physical layout, the schema-backed object, but no operation asks which
layout it holds: every map read and write goes through
`Heap::map_layout` (`runtime/src/heap/map_view.rs`), which answers
`MapLayout::Entries` for the sorted array and `MapLayout::Struct` for a named
struct, and `None` for every other value, a tuple included. A struct's keys
come in map key order, `__struct__` among them; `SchemaRegistry::map_keys`
holds that order once per schema.

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
destination. It is `BackendStep::StructUpdate { base, arity, slots }`, which
cannot miss: `fz_struct_copy` copies the object and `CodegenFn::store_field`
stores each replaced slot in place, the same stores a construction uses. For
example, `%{p | y: 5}` with `p` a `Point` of fields `x` and `y` is one copy
and one store at slot 1.

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

## List Ownership

The list link's **alias bit** protects a closed shared spine: a marked cell has
a marked tail. `ListCons::share_spine` stops at the first marked cell, so repeated
publication visits only newly protected cells plus one check per Share edge.
The bit setter and link are private; shared cells cannot relink, and GC relocates
the same logical tail without changing this invariant.

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
grafts the segment at its next dispatch. A singly copied list can remain clear;
repeated forwarding hits and copied container fields protect receiver-side
sharing. The sender's cells are not marked merely because a copy was sent. Self-send copies nothing and the runtime publishes nothing: the
sender's own reference is pushed onto its mailbox (`sched::self_send`). The
mailbox is then a second holder, and the compiler's call-site ownership rule is
what protects it: `construct_call_ownership` (src/compiler2/jobs/body.rs) marks
a send argument `Share` when the continuation retains a name that may alias it,
and Share publishes the spine before the call on every path. The alias bit
remains one-way within a heap.

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

Off-heap binaries and resources have their own atomic reference counts. A
32-byte `ProcBin` stub owns one edge to a `SharedBin`; a resource stub owns one
edge to a `Resource`. Both off-heap objects are 16-ALIGNED, the same invariant
the process heap keeps, and for the same reason: a stub holds the address in
word 0, and word 0 is where Cheney writes a forwarding marker — a pointer with a
set low nibble. At 8-byte alignment half of those addresses have a set nibble
and a live stub would read as forwarded, so the sweep would write into the
object it is releasing. Alignment is what keeps a live pointer and a marker
distinguishable by construction.

The marker is the only use of the low nibble. Each kind names one marker word —
word 1 of a list cons, word 0 of every other kind — whose live value has a clear
low nibble, so "low nibble set" is the whole forwarding test: one read, no
confirming word (`runtime/src/heap/gc/forwarding.rs`). Copying a stub into another heap retains
one edge. Moving it during GC preserves that edge; sweeping an unreachable stub
or dropping its heap releases it. An immediate last release invokes the
allocation's destructor and reclaims its storage. Deferred resource release
reclaims the wrapper and returns its payload for later destructor dispatch,
without invoking the stored C destructor. Static binaries keep a permanent
anchor and use a no-op destructor.

Lifetime tests observe these exact allocations. A retained handle keeps the
pointer valid while checking which heap-owned edges remain. Separate scoped
destructor observations prove actual final release, including GC, cross-heap
sharing and cross-thread release. A retained witness alone does not prove
destruction, and allocations made by another test do not enter either proof.

## Persistent Roots

Anything that outlives a scheduler or GC boundary is held as `AnyValueRef`,
because the ref is self-describing — a scalar ref has no children, a heap ref is
scanned by object layout, and sentinels have no children. The process mailbox is
`VecDeque<AnyValueRef>` (`runtime/src/process.rs`); a parked receive
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
and queues the segment on the receiver's `in_queue`; the receiver grafts it at
its next dispatch (see [scheduler](scheduler-zero-arg-closures.md)):

```text
self-send:                push the sender's own ref onto its mailbox; nothing is copied
cross-process, parked:    run the receiver's matcher on the sender's ref;
                          on a hit, gift the bound values (nothing when the clause
                          binds none) and wake the receiver; on a miss, gift the
                          whole message, which joins the receiver's mailbox when
                          it drains its in-queue
cross-process, not waiting: gift the whole message; it joins the receiver's
                          mailbox when it drains its in-queue
```

There is no scalar side path inside send.
