# Range

`Range` is an integer range value (`first..last//step`). It is a normal
schema-backed Struct, not a dedicated heap tag, so it rides the same struct
machinery as tuples and other `defstruct` types. The pieces that matter:

- **Source** (`src/modules/runtime_library/range.fz`): the `defstruct`, the
  `@type` record, `Range.new/3`, the scalar arithmetic helpers, and the
  `Enumerable` implementation.
- **Schema** (`runtime/src/heap/schema.rs`): the named `Range` struct layout
  (`first`, `last`, `step`), shared by interpreter, JIT, and AOT.
- **Constructor path**: `%Range{...}` and the `..` / `..//` operators desugar
  to `Range.new/3`, which lowers to `Prim::MakeStruct`.
- **Field read**: `range.first` rides ordinary struct dot-access — no
  Range-specific accessors.
- **Renderer** (`runtime/src/any_value::debug`): prints Elixir-style range
  literals for inspect/`dbg`.

## Source surface

`range.fz` declares `defstruct [:first, :last, :step]` and the record type
`@type t :: %Range{first: integer, last: integer, step: integer}`.
`Range.new/3` is `fn new(first, last, step), do: %Range{first: first, last:
last, step: step}` and is specified to return `Range.t`.

`Kernel.range/3` is an ordinary fz wrapper: `fn range(first, last, step), do:
Range.new(first, last, step)`. No host constructor exists; nothing in the Range
path calls a host extern to build the value.

## From literals to a struct

The frontend macro pass desugars range operators before lowering. `first..last`
(`BinOp::Range`) becomes `Range.new(first, last, 1)`. The stepped form
`first..last//step` (`BinOp::RangeStep`) arrives with its left side *already*
desugared to a `Range.new(first, last, 1)` call (because `..` binds tighter than
`//`); the pass reads `first`/`last` back out of that call and rebuilds
`Range.new(first, last, step)`.

`%Range{...}` lowers in `lower_struct` (`src/ir_lower/expr.rs`) to
`Prim::MakeStruct { module, fields }`. Fields are ordered to match the
`defstruct` declaration order pulled from `LowerCtx::struct_schemas`; a field
absent from the literal is filled with `Const::Nil`. The compiler carries
`defstruct` declarations into `Module::struct_schemas` (a `BTreeMap<String,
Vec<String>>` of qualified name -> field order).

`MakeStruct` allocates the named schema and writes ordinary `AnyValue` fields in
declaration order:

- The interpreter (`src/ir_interp/prim.rs`) looks up `module.struct_schemas`,
  registers `Schema::named_struct(name, fields)` in the process registry, then
  allocates and writes each field at `i * 8`.
- The JIT (`src/ir_codegen/prim.rs`) reads a baked schema id from
  `env.named_schema_ids` and allocates against it.
- AOT bakes a named-schema table (`compiled.rs` `named_schemas`); the emitted
  `main` calls `fz_aot_register_named_schemas` (registering each
  `Schema::named_struct` in the deterministic order codegen baked the ids)
  before it runs user code, so runtime schema ids match the ids iconst'd into
  the CLIF.

The shared layout lives in `Schema::range()`: a `named_struct` with fields
`first`, `last`, `step` at offsets 0, 8, 16, all `FieldKind::AnyValue`, under
`Schema::RANGE_NAME = "Range"`.

## Reading a field

`range.first` is plain struct dot-access. The parser desugars `m.k` to the
atom-keyed index `m[:k]` (`src/parser/expressions.rs`), which lowers to
`Prim::MapGet`. The runtime `MapGet` (`fz_map_get_value_ref` in
`runtime/src/ir_runtime.rs`) special-cases a struct subject with an atom key:
it resolves the atom to a field name and projects via
`read_struct_named_field_ref`. So `range.first` reads the `first` field through
the same path any struct field uses; the interpreter mirrors this for
`Prim::StructField`.

## Field types through the planner

The record type supplies the per-field type facts. During resolve,
`collect_struct_field_types` (`src/frontend/resolve.rs`) checks the record
against the `defstruct` schema (every record field must exist in the schema,
no duplicates, every schema field must be present) and records
`Module::struct_field_types` for `Range` as `[(first, integer), (last,
integer), (step, integer)]`.

Lowering turns those facts into an opaque tuple. `struct_opaque_inners`
(`src/ir_lower/mod.rs`) builds, in schema order, the tuple `{integer, integer,
integer}` and stores it in `Module::opaque_inners` under the key
`impl-target::Range`.

The planner uses this to type field reads. `Prim::MakeStruct` types as the
opaque singleton `impl-target::Range`; `type_struct_field`
(`src/ir_planner/prim.rs`) recovers that tag, finds the field's index in the
schema order, and projects the matching component of the `impl-target::Range`
tuple. After a `%Range{...}` match, `first`, `last`, and `step` therefore read
back as `integer`.

## Equality

Range equality is plain struct equality (`eq_value` -> `eq_struct` in
`runtime/src/ir_runtime.rs`): identical bits short-circuit true; otherwise two
structs are equal only when their schema ids match and every `AnyValue` field
is recursively equal. There is no Range-specific equality case, so a Range
compares equal to another value exactly when both are Range structs with equal
`first`/`last`/`step`.

## Rendering

The value renderer (`render` -> `render_struct` -> `render_range` in the
`debug` module of `runtime/src/any_value.rs`, reached from `fz_dbg_value`)
recognizes the `Range` schema name and prints Elixir-style range literals. It
reads the three integer fields via `Heap::range_fields`. Step `1` renders as
`first..last`; every other step renders as `first..last//step`, including
negative steps such as `10..1//-1`.

## Enumerable

`range.fz` implements `Enumerable` for `Range`. Each `defimpl` callback lowers
into a protocol-owned function whose module is `protocol.child(target)` —
`Enumerable.Range` — giving names like `Enumerable.Range.reduce/3`,
`Enumerable.Range.count/1`, `Enumerable.Range.member?/2`, and
`Enumerable.Range.slice/1`. Those bodies destructure `%Range{first: first,
last: last, step: step}` at the boundary, then delegate to small scalar `Range`
helpers over `first`/`last`/`step`:

- `reduce/5` drives the Enumerable reduce protocol (`:cont` / `:halt` /
  `:suspend` accumulator threading) via the private `reduce_cont` / `reduce_step`
  recursion.
- `count/3` is O(1) arithmetic: `((last - first) / step) + 1`, or `0` when the
  range is empty.
- `member?/4` is arithmetic: a bounds check plus `(value - first) % step == 0`,
  with no iteration.
- `slice/6` builds the Elixir-compatible slice list by stepping `start * step`
  forward and collecting `amount` elements.
