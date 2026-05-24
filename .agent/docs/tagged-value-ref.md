# Tagged Value References

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
TaggedValueRef = one opaque word that says "here is a value"
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
`TaggedValueRef`.

## Why This Helps

The old shape was drifting toward many almost-identical wrappers. Each one
tried to answer the same question in a slightly different way: "what value is
this word?"

The better answer is to stop returning copied value parts from heap reads. If a
map already stores the value, `map_get` can return a tagged reference to that
stored value.

```text
fz_map_get(map, key) -> TaggedValueRef
fz_list_head(list) -> TaggedValueRef
fz_struct_get_field(tuple, field) -> TaggedValueRef
```

The interpreter, REPL, JIT, and AOT code can all call the same API. They get the
same opaque value reference back.

## Examples

Imagine a map contains this entry:

```text
:answer => 42
```

The map stores the integer payload somewhere in the heap. `fz_map_get` returns a
tagged reference to that stored integer:

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

Typed fast paths can be fused later:

```text
fz_map_get_int(map_ref, key_ref) -> i64
fz_map_get_float(map_ref, key_ref) -> f64
fz_map_get_atom(map_ref, key_ref) -> atom id
```

Those are optimizations over the same semantics. They panic if the stored value
has the wrong type. They do not create a second value model.

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

## Opaque Representation

`TaggedValueRef` is opaque. Callers do not inspect or construct it by hand.

Use functions like:

```text
fz_ref_tag(value_ref)
fz_ref_load_int(value_ref)
fz_ref_load_float(value_ref)
fz_ref_load_atom(value_ref)
fz_ref_as_map(value_ref)
fz_ref_as_list(value_ref)
```

The exact pointer format can differ by architecture.

The tag values are semantic and platform-independent:

```text
0 = Null
1 = Int
2 = Float
3 = Atom
4 = EmptyList
5 = List
6 = Map
7 = Struct
8 = Closure
9 = Binary
10 = Resource
...
```

The bit range used to store those tag values is platform-specific:

```text
arm64/TBI:     tagged = address | (tag << 56)
x86_64/LAM48: tagged = address | (tag << 48)
x86_64/LAM57: tagged = address | (tag << 57)  // fewer tag bits available
```

That difference should not matter to the compiler or interpreter. The API owns
packing, unpacking, and clearing. `fz_ref_tag(value_ref)` returns the same tag
value on every platform even if the tag lives in different address bits.

The portable rule is:

```text
Never dereference a TaggedValueRef directly.
Always go through the TaggedValueRef API.
```

Containers appear to store `TaggedValueRef`s. This is a logical API rule, not a
physical storage mandate. Containers may use tighter object-local layouts. A
list can keep a raw head payload and pack the head kind into the link word. A
map can keep raw key/value words plus local tag metadata. The projection API is
what makes those container fields appear as `TaggedValueRef` when dynamic code
reads them.

## GC Rule

A `TaggedValueRef` can point into the moving process heap. That means it is a
temporary reference.

It must not cross:

- allocation
- yield
- GC
- arbitrary runtime calls that may allocate or yield

unless it has been stored in a traced root form.

Only heap-object tagged value refs are GC roots:

```text
Map
List
Struct
Closure
Binary
Resource
```

Scalar refs point at scalar payloads inside some heap/container object. They are
not independent roots.

## Persistent Roots

Anything that survives scheduler or GC boundaries needs a traced root shape.
That includes mailboxes, parked receive pins, matcher outputs, and scheduler
handoff values.

The target implementation uses `TaggedValueRef` for that:

```text
TaggedValueRef
```

The important part is that every dynamic stored value is self-describing.
Scalar refs point at boxed scalar payloads and have no children. Heap-object
refs point at heap objects and are scanned by object layout. Sentinels have no
children.

Older split carriers are transitional debt from split storage. Mailboxes,
parked receive matchers, pinned receive snapshots, and matcher outputs now use
`TaggedValueRef`; remaining split shapes should stay layout-local until they
disappear. Map construction no longer has a process-root builder; it is a fold
of immutable put operations.

There should not be separate mailbox, matcher, interpreter, or codegen value
representations with different conversion rules.

`send` is an `any` boundary. The caller boxes a known scalar only when it must
be sent as `any`, then calls `fz_send_ref(pid, msg_ref)`. The runtime either
hands that ref to the waiting matcher or deep-copies the tagged ref into the
receiver heap before enqueueing it. There is no special scalar side path inside
send.

## Design Law

There is one value reference API:

```text
TaggedValueRef
```

Heap refs are a subset of it.

Interpreter, REPL, JIT, and AOT all use it.

Architecture-specific pointer tricks stay hidden behind the API.

Do not reintroduce parallel value wrappers that are 95% the same. That last 5%
is where bugs live.
