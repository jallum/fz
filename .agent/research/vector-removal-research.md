# Vector Removal Research

## Goal

Remove heap vector kinds before the TaggedValueRef cutover.

Vectors are not part of the basic BEAM-like value set we want to stabilize.
Keeping them through the representation migration adds extra heap tags, GC
cases, BIFs, parser/type-system surface, and tests.

## Retired Runtime Surface

Runtime support had been spread across:

- `runtime/src/fz_value.rs`
  - four vector heap tags.
  - four vector value-kind constants.
  - vector pointer packing/unpacking helpers.
  - vector debug rendering
  - object-size dispatch for vector kinds
- `runtime/src/heap.rs`
  - raw, integer, float, byte, and bit vector allocators.
  - GC scan cases that treat vectors as leaf heap objects
- `runtime/src/ir_runtime.rs`
  - the transient vector builder.
  - vector begin, push, finalize, kind-test, and get BIFs.
- `runtime/src/process.rs`
  - per-process transient vector-builder state.

## Retired Compiler Surface

Compiler/type/parser support had been spread across:

- `src/ast.rs`
  - vector literal AST node.
- `src/fz_ir.rs`
  - vector literal prim.
- `src/ir_typer.rs`
  - vector kind rewrite pass.
  - vector element typing.
- `src/types.rs`
  - vector element enum.
  - vector type constructor.
- `src/concrete_types.rs`
  - vector basic bits.
  - vector constructors and type tests.
- `src/type_expr/parser.rs`
  - the user-facing vector type constructor.
- `src/runtime.fz`
  - vector get wrapper.
- `src/bitstr.rs`
  - byte-vector checks for binary fields.

## Docs/Tests Surface

Vector references are present in:

- `guides/memory.html`
- `tests/fixture_matrix.rs`
- `src/ir_typer_tests.rs`
- `src/type_expr/tests.rs`
- `src/ir_codegen_tests.rs`

## Implemented Removal

Vector removal should happen before the hard representation cut.

The implementation removes the runtime heap tags, allocation routines, BIFs,
builder state, AST/IR forms, type constructors, prelude wrapper, fixtures, and
tests for the vector feature. The parser now rejects the old vector sigils
directly, and the type-expression parser no longer recognizes the old
user-facing vector type constructor.

Some words like "vector" remain legitimate for ordinary Rust collections or
comments. The gate targets retired language/runtime feature identifiers, not
every English use of "vector".

## Bitstring Caveat

`src/bitstr.rs` used to treat byte-aligned bitstrings as byte-vector values.
That dependency is gone: byte-aligned bitstring construction now returns
`Value::Binary`, and binary/bits encoding reads either `Value::Binary` or
`Value::BitStr` directly.
