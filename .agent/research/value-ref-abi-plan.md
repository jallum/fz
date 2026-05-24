# One-Word ValueRef ABI Research

## Question

Why did quicksort grow from the `origin/main` budget of `361` CLIF
instructions to roughly `1500`, and what representation change removes the
regression without reintroducing value-model drift?

## Finding

The regression is not caused by quicksort doing more logical work. The call
graph is materially the same: four `partition` specializations, two `qsort`
specializations, and the same continuation chain.

The cost comes from the generic generated-code value shape:

```text
current generic ABI: raw_payload, kind_byte
target generic ABI:  value_ref
```

The branch repeatedly does this:

```text
split value parts -> pack TaggedValueRef -> call helper
helper returns TaggedValueRef -> unpack value parts -> carry split parts
```

That defeats the point of `TaggedValueRef`. A tagged reference is a singular
runtime value. Generated code should not carry the stamp and envelope
separately.

## Measured Smoke

Current branch quicksort telemetry:

```text
main:             121
append:            75
partition x4:     836
qsort x2:         158
continuations:    337
```

`origin/main` quicksort telemetry:

```text
main:              38
append:            21
partition x4:     204
qsort x2:          36
continuations:     62
```

The worst instruction mix on the branch is glue:

```text
228 band_imm
174 select
131 icmp_imm
 57 uextend
 56 bor
 38 ireduce
```

That is the shape-conversion toll.

## Correct Model

There is one semantic value model, but not one physical storage layout.

Generated code and runtime helper boundaries carry one opaque word:

```text
ValueRef = TaggedValueRef word
```

Typed fast lanes are allowed when statically proven:

```text
RawInt = i64
RawF64 = f64
```

Persistent scheduler and GC boundaries use a root shape:

```text
RootValue = scalar payload + kind, or heap pointer + kind
```

Heap objects use layout-local metadata. This is intentionally not the same
thing as a public tagged reference.

## The Important Distinction

A `TaggedValueRef` tag describes the value addressed by the pointer:

```text
tag = Int
ptr = address of stored i64 payload
```

A list cons link tag describes the other payload word in the same cell:

```text
offset 0: head_payload
offset 8: next_pointer_with_head_kind
```

Mental model:

```text
Cons {
  value: head_payload,
  tag:   kind of head_payload,
  next:  pointer to next cons, or null
}
```

That incongruity is correct because the cons layout owns it. It is private
object-local metadata, not a runtime value reference.

Structs, maps, and closures follow the same principle:

```text
Struct/Tuple:
  field payload words + schema/local field kind metadata

Map:
  key/value payload words + packed key/value kind bytes

Closure/Continuation:
  code pointer + capture payload words + capture kind metadata
```

## What Must Not Exist

The following shapes recreate the regression:

```text
ArgRepr::Tagged with ABI arity 2
LoweredValue { value, kind } as the normal generated value
generic helper signatures taking raw, kind
generic helper signatures returning raw, kind
normal-path pack/unpack helpers around every heap read
ValueSlot imports in codegen as a value carrier
```

Layout-local storage helpers may still use a small raw+kind record internally.
That record must not be the compiler/runtime value ABI.

## GC Walkthrough

GC traces by object layout.

For a list:

```text
head = cons.word0
link = cons.word1
head_kind = low4(link)
next = clear_low4(link)

if head_kind is heap:
  trace head as heap pointer

if next != 0:
  trace next cons
```

The local tag lets GC skip scalar heads without consulting a generic slot
object.

For a struct:

```text
for each field in schema:
  payload = field word
  kind = field metadata
  if kind is heap:
    trace payload
```

For a map:

```text
for each entry:
  key_kind, value_kind = packed tag byte
  trace key payload if key_kind is heap
  trace value payload if value_kind is heap
```

For a closure:

```text
code pointer is not a heap root
for each capture:
  payload = capture word
  kind = capture metadata
  if kind is heap:
    trace payload
```

For `RootValue`:

```text
if kind is heap:
  trace value as heap pointer
else:
  leave scalar payload unchanged
```

## Mental Walkthrough: Quicksort

Target list head:

```text
list_ref -> fz_list_head_ref(list_ref) -> head_ref
head_int = fz_ref_load_int(head_ref)
```

Target list tail:

```text
list_ref -> fz_list_tail_ref(list_ref) -> tail_ref
```

Target tuple projection:

```text
pair_ref = partition(...)
lo_ref = fz_struct_get_field_ref(pair_ref, 0)
hi_ref = fz_struct_get_field_ref(pair_ref, 8)
qsort(lo_ref)
qsort(hi_ref)
```

Target continuation capture:

```text
execution value: one-word ValueRef
persistent capture: closure layout writes payload + local kind metadata
resume: closure layout accessor reconstructs a ValueRef for execution
```

The split exists only while writing or reading object-local storage. It does
not cross function signatures.

## Ticket Strategy

1. Document the invariant and forbidden shapes.
2. Audit GC walkers before changing the generated ABI.
3. Rename the codegen concept from `Tagged` to `ValueRef` without behavior
   changes.
4. Make `ValueRef` one word in generated signatures.
5. Delete normal-path split carriers and pack/unpack tolls.
6. Convert list, tuple, map, continuation, and receive lowering around refs.
7. Confine the storage-local raw+kind record to heap/layout internals.
8. Refresh interpreter value flow around refs.
9. Gate on quicksort and structural searches.

The proud acceptance target is quicksort below `500` CLIF instructions. The
strict regression gate is below `600`; anything higher means a split-value toll
survived.
