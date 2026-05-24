# TaggedValueRef Research

## Goal

Replace the current family of raw+kind value wrappers with one opaque
`TaggedValueRef` API shared by the interpreter, REPL, JIT, and AOT paths.

The target is not a compatibility bridge. The target is one heap/value model:

```text
TaggedValueRef = opaque tagged reference to a value
```

Scalar refs point at scalar payloads. Heap-object refs point at heap objects.
Heap refs are therefore a subset of tagged value refs.

## Current Problem

The current implementation has many almost-equivalent value representations:

- `FzValue`
- `FzValueParts`
- `MailboxSlot`
- `InterpValue`
- `StrictValue`
- `MatcherValue`

They are not exactly equivalent, which is the problem.

Examples:

- `FzValue` is `raw + ValueKind`.
- `FzValueParts` is ABI-shaped `raw + u8 kind`.
- `MailboxSlot` claims raw payload plus kind, but stores heap values as
  already-tagged heap pointer words.
- `StrictValue` and `MatcherValue` are both Cranelift SSA raw+kind pairs.
- `InterpValue` splits integers and floats out separately, then repeatedly
  converts back into `FzValue`.

The last 5% of difference creates conversion bugs and local bridge code.

## Target Model

The unified API returns a tagged reference word:

```text
fz_map_get(map_ref, key_ref) -> TaggedValueRef
fz_list_head(list_ref) -> TaggedValueRef
fz_list_tail(list_ref) -> TaggedValueRef
fz_struct_get_field(struct_ref, field) -> TaggedValueRef
```

The tag values are semantic and platform-independent:

```text
Null
Int
Float
Atom
EmptyList
List
Map
Struct
Closure
Bitstring
ProcBin
Resource
```

Vector tags are intentionally omitted. Vectors are slated for removal before
the representation cutover.

## Platform Packing

The API owns packing and unpacking. Callers must not inspect or dereference a
tagged value ref directly.

The same tag values can be packed at different shifts by platform:

```text
arm64/TBI:     tag << 56
x86_64/LAM48: tag << 48
x86_64/LAM57: tag << 57
```

The implementation can choose the correct packing strategy per target. The
compiler/interpreter only see API operations:

```text
fz_ref_tag(ref) -> same semantic tag value everywhere
fz_ref_load_int(ref) -> i64
fz_ref_load_float(ref) -> f64
fz_ref_load_atom(ref) -> atom id
fz_ref_as_map(ref) -> TaggedValueRef
```

## Heap Layout Implications

Existing storage is split by layout:

- list head payload is `ListCons.head`; head kind is packed into low bits of
  `ListCons.link`.
- list tail is already a list reference/sentinel shape.
- map keys and values live in dense `u64` arrays; key/value kinds live in a
  packed tag byte.
- struct/tuple fields are raw `u64` slots; kind bytes live in schema-derived
  side-band storage.
- closure captures are raw `u64` slots plus side-band capture kind bytes.

The new read APIs do not need to copy these into `{ raw, kind }`. They can
return a `TaggedValueRef`:

- scalar result: tagged ref points at the stored scalar payload slot.
- heap-object result: tagged ref points at the heap object itself.
- empty list/null: tagged sentinel.

This avoids stack out buffers and avoids repeated word/kind lookups.

## Persistent Storage vs Temporary Refs

`TaggedValueRef` is a temporary reference into a moving heap. It must not cross:

- allocation
- yield
- GC
- arbitrary runtime calls that may allocate or yield

unless rooted by a persistent storage form that the GC traces.

This is the key distinction:

```text
TaggedValueRef: temporary API result / operand
persistent storage: mailbox, root slab, heap fields/captures/maps/lists
```

Persistent storage still needs to be traceable. The exact persistent format can
be a heap-owned value slot or a direct heap-object ref where the layout allows
it, but it must not be a second public value model.

## GC Rule

Only heap-object tagged value refs are roots.

Scalar refs point at scalar payload inside an existing heap/container object.
They are not independent roots.

Persistent roots must let the GC find and forward heap-object refs. Temporary
interior scalar refs do not participate in GC.

## Runtime Surface

Core BIFs should be one-word in/out where possible:

```text
fz_map_get(map_ref, key_ref) -> TaggedValueRef
fz_list_head(list_ref) -> TaggedValueRef
fz_list_tail(list_ref) -> TaggedValueRef
fz_struct_get_field(struct_ref, field) -> TaggedValueRef
```

Projection helpers:

```text
fz_ref_tag(ref) -> u8
fz_ref_load_int(ref) -> i64
fz_ref_load_float(ref) -> f64
fz_ref_load_atom(ref) -> u64
fz_ref_as_heap(ref) -> TaggedValueRef
```

Fused typed BIFs can exist later for performance:

```text
fz_map_get_int(map_ref, key_ref) -> i64
fz_list_head_float(list_ref) -> f64
```

These are optimizations over the same semantics, not a second model.

## Hard Cut Strategy

Do not switch one family at a time in production paths. The old and new physical
value layouts are incompatible enough that mixed mode would recreate bridge
debt.

The safe plan:

1. Build and test the new primitives against the heap in isolation.
2. Remove vector heap kinds to shrink the target surface.
3. Create the hard-cut acceptance gate before the cutover.
4. Rip out or rename old value ABI/types so they stop compiling.
5. Work compiler-error clusters as child tickets.
6. Make every discovered child ticket block the gate.

The hard-cut campaign should be a worklist, not one hidden monster ticket.

