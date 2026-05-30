# Range as a Struct

Decision (fz-g58.0.2): the Elixir `Range` value — what `first..last` and
`first..last//step` construct — is represented as an ordinary schema-tagged
struct, **not** a new runtime tag. It carries three fields: `first`, `last`,
`step`.

## Big Idea

The runtime value model already has a general aggregate: `TAG_STRUCT` (`0x3`),
a heap object whose layout is described by a registered schema (see
[any-value](any-value.md) and `runtime/src/any_value.rs`). Tuples and tagged
records are structs. A `Range` is just one more struct schema. Nothing about
ranges needs a dedicated tag, payload format, equality routine, or printer —
those already exist for structs and apply unchanged.

## Why not a new heap tag

A new tag (`TAG_RANGE`) would force a parallel change in every place that
switches on the tag set: allocation, GC tracing/forwarding, equality, the
`dbg`/inspect printer, the interpreter's value enum, and the codegen value
representation — across all three execution paths. That is real churn for zero
expressive gain, because a 3-field struct already models a range exactly.

Reusing `TAG_STRUCT` means:

- **Equality is free.** Struct equality is schema-driven and compares fields;
  two ranges are equal iff their `first`/`last`/`step` match. No new routine.
- **GC is free.** A range's fields are plain integers; the existing struct
  tracer handles it.
- **Construction is ordinary.** The `..` / `..//` desugar (fz-g58.3.2) lowers to
  a normal struct construction — the same path tuples take.
- **Three-path parity is structural.** No backend learns a new value kind.

## Policy

- The `..` and `..//` operators desugar to a `Range` struct construction in the
  frontend (fz-g58.3.2); they are not first-class IR.
- `Enumerable` is implemented for `Range` as an ordinary `defimpl`
  (fz-g58.5.1): `reduce` walks `first` toward `last` by `step`, `count` is
  arithmetic and O(1), `member?` is an arithmetic bounds+stride check.
- Inspect/`dbg` rendering must match Elixir's (`1..10`, `1..10//2`); this is the
  one struct schema whose printer is customized rather than using the default
  record rendering. Pin it with an oracle fixture (see [fixtures](fixtures.md)).
