# ValueRef ABI

## ELI5

Running code should carry one value-shaped thing:

```text
ValueRef
```

It is an opaque tagged word. The tag says what kind of value the reference
names, and the address says where that value can be read.

Do not carry this as two pieces:

```text
raw_payload, kind_byte
```

That split is storage detail. It is not the generated-code ABI.

## Three Lifetimes

The same fz value can live in three different places. The lifetime chooses the
shape.

```text
Execution:
  ValueRef
  One opaque word crossing generated/runtime helper boundaries.

Persistent roots:
  RootValue
  Scheduler, mailbox, parked receive, and GC handoff storage.

Heap object internals:
  Layout-local payload words plus layout-local metadata.
```

The names matter because the wrong shape caused the quicksort regression.

## Execution Values

Generated code has three lanes:

```text
ValueRef  // one i64 TaggedValueRef word
RawInt    // proven integer fast lane
RawF64    // proven float fast lane
```

`ValueRef` is one word. Always.

Runtime helpers that traffic in generic values use refs:

```text
fz_list_head_ref(list_ref) -> value_ref
fz_list_tail_ref(list_ref) -> list_ref
fz_struct_get_field_ref(struct_ref, offset) -> value_ref
fz_map_get_ref(map_ref, key_ref) -> value_ref
```

Typed projections are explicit:

```text
fz_ref_load_int(value_ref) -> i64
fz_ref_load_float(value_ref) -> f64
fz_ref_load_atom(value_ref) -> atom id
fz_ref_tag(value_ref) -> tag
```

Typed fused helpers are allowed as optimizations over the same model:

```text
fz_list_head_int(list_ref) -> i64
fz_map_get_int(map_ref, key_ref) -> i64
```

They do not create a second generic value shape.

## Object-Local Metadata

Heap layouts own their metadata. That metadata can use pointer bits flexibly
because it is private to the layout.

List cons cells intentionally use their link word differently from public
`TaggedValueRef`:

```text
offset 0: head_payload: u64
offset 8: next_pointer_with_head_kind: u64
```

Here the low tag bits describe `head_payload`, not the next pointer itself.

Mental model:

```text
{
  next:  pointer to next cons, or null
  tag:   kind of this cell's head payload
  value: head payload
}
```

Structs, maps, and closures do the same kind of thing with layouts that suit
their access patterns:

```text
Struct/Tuple:
  payload words + field kind metadata

Map:
  key/value payload words + packed key/value kind bytes

Closure/Continuation:
  code pointer + capture payload words + capture kind metadata
```

This is not a contradiction. Public refs are public refs. Object-local metadata
is object-local metadata.

## Persistent Roots

`ValueRef` may point into the moving heap. It must not survive allocation,
yield, GC, or arbitrary runtime calls unless it has been stored in a traced
root shape.

Roots need to represent scalars too, and scalars are not independent heap
objects. That is why roots keep payload plus kind:

```text
RootValue {
  value: scalar payload or heap pointer
  kind:  semantic value kind
}
```

This is a root record, not the runtime value ABI.

## GC

GC traces by object layout.

For a list:

```text
head_payload = cons.word0
link = cons.word1
head_kind = low4(link)
next = clear_low4(link)

if head_kind is heap:
  trace head_payload
if next != 0:
  trace next
```

For a struct, map, or closure, the walker reads that layout's local metadata
and traces only heap-like payloads.

For a root, the walker reads `kind` and traces `value` only when the kind is a
heap kind.

## Forbidden Shapes

These are the debt we are removing:

```text
generic generated values as raw, kind
ArgRepr::Tagged with ABI arity 2
LoweredValue { value, kind } as the normal codegen carrier
helper APIs that return generic values as parts
normal-path pack ValueRef, call helper, unpack ValueRef
ValueSlot as a public/compiler/interpreter value model
```

If code needs raw payload plus kind, it must be visibly inside a heap layout or
a persistent root operation.

## Quicksort Gate

Quicksort is the smoke test because it exercises:

- list head/tail
- cons construction
- tuple return and projection
- continuation captures
- recursive calls

The old main budget was `361` CLIF instructions. The split-value branch grew
to roughly `1500`. The one-word ValueRef arc should bring it below `600`, with
a proud target below `500`.
