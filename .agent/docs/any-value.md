# Any Values

## ELI5

A value in fz is something like:

- an integer
- a float
- an atom
- a list
- a map
- a tuple/struct
- a resource
- a binary

Some of those values are tiny scalar payloads. An integer is just 64 bits. A
float is just 64 bits. An atom is an id. Those payloads do not have spare bits
we can steal without making the value smaller.

Other values live on the heap. A map, list cell, tuple, resource, or binary is
an object in the process heap. A reference to one of those objects is a pointer.

The simple idea is:

```text
AnyValueRef = one opaque word that says "here is a value"
```

The tag says what kind of value it is. The pointer/address says where to find it.

For scalars, the address points at the scalar payload:

```text
Int ref   -> points at an i64
Float ref -> points at an f64
Atom ref  -> points at an atom id
```

For heap objects, the address points at the object itself:

```text
Map ref      -> points at a map object
List ref     -> points at a list cell
Struct ref   -> points at a tuple/struct object
Resource ref -> points at a resource object
Binary ref   -> points at a binary object
```

So a heap reference is not a separate idea. It is the heap-object subset of
`AnyValueRef`.

## Why This Helps

The old shape was drifting toward many almost-identical wrappers. Each one
tried to answer the same question in a slightly different way: "what value is
this word?"

The better answer is to stop returning copied value parts from heap reads. If a
map already stores the value, `map_get` can return an any value reference to that
stored value.

```text
fz_map_get(map, key) -> AnyValueRef
fz_list_head(list) -> AnyValueRef
fz_struct_get_field(tuple, field) -> AnyValueRef
```

The interpreter, REPL, JIT, and AOT code can all call the same API. They get the
same opaque value reference back.

## Examples

Imagine a map contains this entry:

```text
:answer => 42
```

The map stores the integer payload somewhere in the heap. `fz_map_get` returns an
any value reference to that stored integer:

```text
let value_ref = fz_map_get(map_ref, atom_answer_ref)

value_ref tag     = Int
value_ref address = address of the stored i64 payload
```

Then the caller can project it:

```text
fz_ref_load_int(value_ref) -> 42
```

If the map contains another map:

```text
:child => %{ :x => 1 }
```

then the returned reference is already a map reference:

```text
let child_ref = fz_map_get(parent_map_ref, atom_child_ref)

child_ref tag     = Map
child_ref address = address of child map object
```

No extra two-part result is needed.

## One API For Both Worlds

The Rust interpreter can use this directly:

```text
let value_ref = fz_map_get(map_ref, key_ref)
let n = fz_ref_load_int(value_ref)
```

Generated JIT/AOT code can use the same calls:

```text
call fz_map_get
call fz_ref_load_int
```

Typed fast paths are fused helpers:

```text
fz_map_get_int(map_ref, key_ref) -> i64
fz_map_get_float(map_ref, key_ref) -> f64
fz_map_get_atom(map_ref, key_ref) -> atom id
```

They panic if the stored value has the wrong type. They do not create a second
value model.

Typed writes are not dynamic reads in reverse. If the caller already knows it
has an `i64`, it should call the typed write path and let the container store
the payload in its compact local layout:

```text
fz_map_put_int(map_ref, key_ref, value_i64)
fz_list_cons_int(value_i64, tail_ref)
```

Do not construct an `Int` ref just to pass it to a write API. `*_put_ref` /
`*_cons_ref` paths are for values that are already dynamic heap/sentinel refs.
They should reject scalar refs to keep the representation honest.

## Generated Code ABI

Generated code has three value lanes:

```text
ValueRef  // one i64 AnyValueRef word
RawInt    // proven integer fast lane
RawF64    // proven float fast lane
```

`ValueRef` is one word. Always.

Typed lanes avoid boxing while the type is known. Boxing is for unavoidable
`any` boundaries:

```text
send(pid, 42)
  box 42 because send takes any
  store ValueRef(Int) in the mailbox
```

Do not carry a generic value as two ABI pieces:

```text
raw_payload, kind_byte
```

That shape is storage detail. It is not the generated-code ABI.

## Opaque Representation

`AnyValueRef` is opaque. Callers do not inspect or construct it by hand.

Use functions like:

```text
fz_ref_tag(value_ref)
fz_ref_load_int(value_ref)
fz_ref_load_float(value_ref)
fz_ref_load_atom(value_ref)
fz_map_get_ref(map_ref, key_ref)
fz_list_head_ref(list_ref)
```

The exact pointer format can differ by architecture.

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

The empty list is represented as tag `List` with a null address. The runtime
still has an object-storage `EMPTY_LIST` tail sentinel, but that sentinel is not
the public tagged-pointer representation.

The bit range used to store those tag values is platform-specific:

```text
arm64/TBI:         tagged = address | (tag << 56)
x86_64 canonical: tagged = address | (tag << 57)
```

That difference should not matter to the compiler or interpreter. The API owns
packing, unpacking, and clearing. `fz_ref_tag(value_ref)` returns the same tag
value on every platform even if the tag lives in different address bits.

The portable rule is:

```text
Never dereference an AnyValueRef directly.
Always go through the AnyValueRef API.
```

Containers appear to store `AnyValueRef`s. This is a logical API rule, not a
physical storage mandate. Containers may use tighter object-local layouts. A
list can keep a raw head payload and pack the head kind into the link word. A
map can keep raw key/value words plus local tag metadata. The projection API is
what makes those container fields appear as `AnyValueRef` when dynamic code
reads them.

Examples:

```text
List cons:
  head payload word
  next pointer word with local head kind bits

Map:
  key/value payload words
  packed local key/value kind metadata

Closure:
  raw code pointer
  capture payload words
  local capture kind metadata
```

Public refs are public refs. Object-local metadata is object-local metadata.

## GC Rule

A `AnyValueRef` can point into the moving process heap. That means it is a
temporary reference.

It must not cross:

- allocation
- yield
- GC
- arbitrary runtime calls that may allocate or yield

unless it has been stored in a traced root form.

Only heap-object any value refs are followed as heap edges:

```text
Map
List
Struct
Closure
Binary
ProcBin
Resource
```

Scalar refs point at scalar payloads inside some heap/container object. They are
copied when they are durable root slots, but they are not followed as child
pointers.

GC copies reachable objects as whole objects. It only follows child pointers
when object-local metadata says a payload word is heap-shaped.

```text
copy bytes:   every reachable object moves or survives as a unit
follow edges: only heap-shaped payload slots become child roots
```

Scalar payloads can look like addresses. That does not make them pointers. The
layout tag/kind is the authority.

## Persistent Roots

Anything that survives scheduler or GC boundaries needs a traced root shape.
That includes mailboxes, parked receive pins, matcher outputs, and scheduler
handoff values.

The implementation uses `AnyValueRef` for that:

```text
AnyValueRef
```

The important part is that every dynamic stored value is self-describing.
Scalar refs point at boxed scalar payloads and have no children. Heap-object
refs point at heap objects and are scanned by object layout. Sentinels have no
children.

Older split carriers are transitional debt from split storage. Mailboxes,
parked receive matchers, pinned receive snapshots, and matcher outputs now use
`AnyValueRef`; remaining split shapes should stay layout-local until they
disappear. Map construction no longer has a process-root builder; it is a fold
of immutable put operations.

## Forbidden Shapes

These are normal-path bugs, not alternate models:

```text
generic generated values as raw, kind
ArgRepr::ValueRef with ABI arity 2
helper APIs that return generic values as parts
normal-path pack ValueRef, call helper, unpack ValueRef
ValueSlot as a public/compiler/interpreter value model
```

If code needs raw payload plus kind, it must be visibly inside a heap layout.

There should not be separate dynamic value models for mailbox, matcher,
interpreter, or codegen paths.

`send` is an `any` boundary. The caller boxes a known scalar only when it must
be sent as `any`, then calls `fz_send_ref(pid, msg_ref)`. The runtime either
hands that ref to the waiting matcher or deep-copies the any value ref into the
receiver heap before enqueueing it. There is no special scalar side path inside
send.

## Design Law

There is one value reference API:

```text
AnyValueRef
```

Heap refs are a subset of it.

Interpreter, REPL, JIT, and AOT all use it.

Architecture-specific pointer tricks stay hidden behind the API.

Do not reintroduce parallel value wrappers that are 95% the same. That last 5%
is where bugs live.
