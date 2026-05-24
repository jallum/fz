# Vector Removal Research

## Goal

Remove heap vector kinds before the TaggedValueRef cutover.

Vectors are not part of the basic BEAM-like value set we want to stabilize.
Keeping them through the representation migration adds extra heap tags, GC
cases, BIFs, parser/type-system surface, and tests.

## Current Runtime Surface

Runtime vector support is visible in:

- `runtime/src/fz_value.rs`
  - `TAG_VEC_I64`
  - `TAG_VEC_F64`
  - `TAG_VEC_U8`
  - `TAG_VEC_BIT`
  - `ValueKind::VEC_*`
  - `tagged_vec_bits`
  - `vec_kind_from_tagged`
  - vector debug rendering
  - object-size dispatch for vector kinds
- `runtime/src/heap.rs`
  - `alloc_vec_raw`
  - `alloc_vec_i64`
  - `alloc_vec_f64`
  - `alloc_vec_u8`
  - `alloc_vec_bit`
  - GC scan cases that treat vectors as leaf heap objects
- `runtime/src/ir_runtime.rs`
  - `VecBuild`
  - `fz_vec_begin`
  - `fz_vec_push_typed`
  - `fz_vec_finalize`
  - `fz_vec_is_kind`
  - `fz_vec_get_typed`
- `runtime/src/process.rs`
  - `vec_builder`

## Compiler Surface

Compiler/type/parser support is visible in:

- `src/ast.rs`
  - vector literal AST node.
- `src/fz_ir.rs`
  - `VecKindIr`
  - vector literal prim.
- `src/ir_typer.rs`
  - `rewrite_vec_kinds`
  - `VectorElem` handling.
- `src/types.rs`
  - `VectorElem`
  - `Types::vec`.
- `src/concrete_types.rs`
  - `BasicBits::VEC_*`
  - vector constructors and type tests.
- `src/type_expr/parser.rs`
  - `vector(integer)`, `vector(float)`, `vector(u8)`, `vector(bit)`.
- `src/runtime.fz`
  - `vec_get` extern wrapper.
- `src/bitstr.rs`
  - byte-vector checks for binary fields.

## Docs/Tests Surface

Vector references are present in:

- `guides/memory.html`
- `tests/fixture_matrix.rs`
- `src/ir_typer_tests.rs`
- `src/type_expr/tests.rs`
- `src/ir_codegen_tests.rs`

## Removal Strategy

Vector removal should happen before the hard representation cut.

Acceptance should reject:

```text
TAG_VEC_
ValueKind::VEC
VecBuild
fz_vec_
alloc_vec_
tagged_vec
vec_kind_from_tagged
vector(
VectorElem
VecKindIr
```

Some words like "vector" remain legitimate for ordinary Rust collections or
comments. The gate should target the language/runtime feature names above, not
every English use of "vector".

## Bitstring Caveat

`src/bitstr.rs` currently expects byte-vector values in at least one path. When
vectors are removed, binary construction must either:

- move to bitstring/procbin values directly, or
- reject the old byte-vector path with a diagnostic until a replacement exists.

This is a known thorny point and should be called out in the vector removal
ticket acceptance criteria.

