# Any Values

## Model

A fz value is one of: integer, float, atom, list, map, tuple/struct, resource,
binary. Some are tiny scalar payloads with no spare bits to steal. Others live
on the heap and are addressed by pointer.

The unifying idea is one opaque runtime word:

```text
AnyValueRef = one opaque word that says "here is a value"
```

The word carries a tag (what kind) and an address (where to find the payload).
Scalar refs point at scalar payloads. Heap refs point at heap objects. A heap
reference is not a separate idea — it is the heap-object subset of
`AnyValueRef`.

```text
Int ref      -> points at an i64
Float ref    -> points at an f64
Atom ref     -> points at an atom id
Map ref      -> points at a map object
List ref     -> points at a list cell
Struct ref   -> points at a tuple/struct object
Resource ref -> points at a resource object
Binary ref   -> points at a binary object
```

The interpreter, REPL, JIT, and AOT paths all pass values through this single
shape.

## Major Pieces

The **public ref API** is the only way callers handle a value. `AnyValueRef`
is opaque. Callers do not inspect or construct it by hand:

```text
fz_ref_tag(value_ref)
fz_ref_load_int(value_ref)
fz_ref_load_float(value_ref)
fz_ref_load_atom(value_ref)
fz_binary_concat(process, left_ref, right_ref)
fz_map_get_ref(map_ref, key_ref)
fz_map_count(map_ref)
fz_map_entry_key(map_ref, index)
fz_map_entry_value(map_ref, index)
fz_list_head_ref(list_ref)
```

**Dynamic reads return refs.** Heap reads do not return copied value parts. If
a map already stores the value, `fz_map_get_ref` returns a ref to that stored
value:

```text
fz_map_get_ref(map, key)             -> AnyValueRef
fz_map_entry_key(map, index)         -> AnyValueRef
fz_map_entry_value(map, index)       -> AnyValueRef
fz_list_head_ref(list)               -> AnyValueRef
fz_struct_get_field_ref(tuple, fld)  -> AnyValueRef
```

`Enumerable.Map` walks the runtime's canonical sorted entry storage with
`fz_map_count`, `fz_map_entry_key`, and `fz_map_entry_value` from source-level
fz code. The entry helpers return refs into immutable map storage; tuple/list
construction copies those values into new containers before publishing them.

`fz_binary_concat` validates byte-aligned binary inputs, copies their payload
bytes into the caller process heap, and returns a binary ref. Allocation still
flows through `Heap::alloc_bitstring`, so large results automatically use the
ProcBin/shared-binary path.

**Typed fast paths** are fused helpers for callers that already know the type.
They panic on mismatch; they do not create a second value model:

```text
fz_map_get_int(map_ref, key_ref)   -> i64
fz_map_get_float(map_ref, key_ref) -> f64
fz_map_get_atom(map_ref, key_ref)  -> atom id
```

**Typed writes** let the caller hand a known scalar straight into the
container's compact local layout, with no detour through a built `Int` ref:

```text
fz_map_put_int(map_ref, key_ref, value_i64)
fz_list_cons_int(value_i64, tail_ref)
```

`*_put_ref` / `*_cons_ref` paths are for already-dynamic refs and reject
scalar refs, to keep the representation honest.

## Walkthrough

A map contains `:answer => 42`. The integer payload lives in the heap. `fz_map_get_ref`
returns a ref to it:

```text
let value_ref = fz_map_get_ref(map_ref, atom_answer_ref)

value_ref tag     = Int
value_ref address = address of the stored i64 payload

fz_ref_load_int(value_ref) -> 42
```

If the map contains another map at `:child`, the returned ref is already a map
ref — no extra two-part result is needed:

```text
let child_ref = fz_map_get_ref(parent_map_ref, atom_child_ref)

child_ref tag     = Map
child_ref address = address of child map object
```

## Generated Code ABI

Generated code has three value lanes:

```text
ValueRef  // one i64 AnyValueRef word
RawInt    // proven integer fast lane
RawF64    // proven float fast lane
```

`ValueRef` is always one word. Typed lanes avoid boxing while the type is
known. Boxing happens only at unavoidable `any` boundaries:

```text
send(pid, 42)
  box 42 because send takes any
  store ValueRef(Int) in the mailbox
```

Every generated-code representation seam must coerce through the runtime value
model. A `ValueRef` flowing into a `RawInt` or `RawF64` slot is unboxed with the
ref API; a raw scalar flowing into a `ValueRef` slot is boxed; matching raw lanes
pass through unchanged. This applies equally to call arguments, continuation
arguments, and typed frame slots. Copying the bits of a `ValueRef(Int)` into a
`RawInt` slot is never valid: the word is a ref, not the integer payload.

## Tags And Platform Packing

The tag values are semantic and platform-independent:

```text
0 = Null
1 = List
2 = Map
3 = Struct
4 = Closure
5 = Bitstring
6 = ProcBin
7 = Resource
13 = Int
14 = Float
15 = Atom
```

The empty list is `List` with a null address. The runtime keeps an
object-storage `EMPTY_LIST` tail sentinel, but that sentinel is not the public
tagged-pointer representation.

The bits used to store the tag are platform-specific:

```text
arm64/TBI:        tagged = address | (tag << 56)
x86_64 canonical: tagged = address | (tag << 57)
```

Callers never see that difference. The API owns packing, unpacking, and
clearing. `fz_ref_tag(value_ref)` returns the same tag value on every
platform.

The portable rule:

```text
Never dereference an AnyValueRef directly.
Always go through the AnyValueRef API.
```

## Container Storage

Containers appear to store `AnyValueRef`s. That is a logical API rule, not a
physical storage mandate. Containers may use tighter object-local layouts. The
projection API is what makes those container fields appear as `AnyValueRef`
when dynamic code reads them.

```text
List cons:
  head payload word
  link word with high alias/head-kind metadata and local next pointer bits

Map:
  key/value payload words
  packed local key/value kind metadata

Closure:
  raw code pointer
  capture payload words
  local capture kind metadata
```

The list link alias bit is a conservative cell-local reuse guard. Runtime
helpers may mark a cons aliased. Internal primitive checks may reject an
aliased cell, but codegen-facing reuse helpers must be total for valid inputs:
if the source cons is still unaliased they may relink it in place; if it is
aliased they must use fallback allocation for a fresh cons with the same head
and the requested tail. GC preserves the bit inside a process heap. Deep copy
creates fresh cells in the destination heap, so copied list cells start
unaliased even when the source cell was marked aliased.

The alias bit is set, or a physical reuse capability is not recorded, when a cons cell is
published outside the single owned rewrite path. A publication includes storing
the cell in another heap object, capturing it in a closure or scheduler-visible
continuation, or crossing a barrier where allocation timing becomes observable.
Native call lowering also marks an argument when the caller passes it to a
callee and keeps the same value in the continuation; that protects examples
like `xs |> reverse(); xs |> map()` from letting the first call rewrite the
list that the continuation will later traverse.
Passing a value to an extern does not publish it: an extern that wants to retain
a value beyond the call must copy it. Cross-process
send and self-send are copy boundaries, not alias boundaries: the sender's
current-process cells need not be marked, and the receiver/mailbox copy is a
fresh unaliased graph. The bit is intentionally one-way inside a heap: once a
cell has been published there, later local code may still read it, but
destructive reuse must fall back to allocation.

Public refs are public refs. Object-local metadata is object-local metadata.

## GC Rule

An `AnyValueRef` can point into the moving process heap. It is a temporary
reference. It must not cross:

- allocation
- yield
- GC
- arbitrary runtime calls that may allocate or yield

unless it has been stored in a traced root form.

Only heap-object refs are followed as heap edges:

```text
Map, List, Struct, Closure, Bitstring, ProcBin, Resource
```

Scalar refs point at scalar payloads inside some heap/container object. They
are copied when they sit in durable root slots, but they are not followed as
child pointers.

GC copies reachable objects as whole objects. It only follows child pointers
when object-local metadata says a payload word is heap-shaped.

```text
copy bytes:   every reachable object moves or survives as a unit
follow edges: only heap-shaped payload slots become child roots
```

Scalar payloads can look like addresses; that does not make them pointers. The
layout tag/kind is the authority.

## Persistent Roots

Anything that survives scheduler or GC boundaries needs a traced root shape.
That includes mailboxes, parked receive pins, matcher outputs, and scheduler
handoff values. The implementation uses `AnyValueRef` for that.

Every dynamic stored value is self-describing. Scalar refs point at boxed
scalar payloads and have no children. Heap-object refs point at heap objects
and are scanned by object layout. Sentinels have no children.

Mailboxes, parked receive matchers, pinned receive snapshots, and matcher
outputs use `AnyValueRef`. Map construction has no process-root builder; it is a
fold of immutable put operations.

## What This Model Keeps Out

These are normal-path bugs, not alternate models:

```text
generic generated values as raw, kind
ArgRepr::ValueRef with ABI arity 2
helper APIs that return generic values as parts
normal-path pack ValueRef, call helper, unpack ValueRef
ValueSlot as a public/compiler/interpreter value model
```

If code needs raw payload plus kind, it must be visibly inside a heap layout.
There is one dynamic value model — not separate ones for mailbox, matcher,
interpreter, or codegen paths.

`send` is an `any` boundary. The caller boxes a known scalar only when it
must be sent as `any`, then calls `fz_send_ref(pid, msg_ref)`. The runtime
either hands that ref to the waiting matcher or deep-copies the ref into the
receiver heap before enqueueing it. There is no special scalar side path
inside send.

Architecture-specific pointer tricks stay hidden behind the API. There are no
parallel value wrappers that are 95% the same — that last 5% is where bugs live.
