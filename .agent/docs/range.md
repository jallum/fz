# Range

fz represents `Range` as a normal schema-backed Struct. It does not have a
dedicated heap tag. The source surface is `defstruct [:first, :last, :step]`
plus `@type t :: %Range{first: integer, last: integer, step: integer}` in
`src/modules/runtime_library/range.fz`. `Range.new/3` constructs
`%Range{first: first, last: last, step: step}` and is specified to return
`Range.t`.

The compiler carries `defstruct` declarations into `Module.struct_schemas`.
`%Range{...}` lowers to `Prim::MakeStruct`, which allocates the registered
schema and writes ordinary `AnyValue` fields in declaration order. JIT and
interp register named schemas directly; AOT emits a named-schema table and
registers it before user code runs, in the same order codegen used for baked
schema ids. Dot access continues to lower through `MapGet`; runtime map-get
treats atom-key lookup on a Struct as named-field projection, so `range.first`
reads the `first` field without Range-specific extern accessors.

The record type supplies the field facts for the struct. Resolve checks it
against the `defstruct` schema, and lowering registers `impl-target::Range`
with an `{integer, integer, integer}` underlying tuple in schema order. Planner
struct-field projection therefore reads `first`, `last`, and `step` back as
integers after a `%Range{...}` match.

`Kernel.range/3` is an ordinary fz wrapper around `Range.new/3`. There is no
`fz_range_new` host constructor.

The frontend desugar pass rewrites `first..last` to `Range.new(first, last, 1)`.
For the literal stepped form `first..last//step`, it rewrites the already-built
`Range.new(first, last, 1)` call to `Range.new(first, last, step)`. No Range
operator path calls a host extern.

Because Range is an ordinary Struct, runtime equality follows the existing
struct equality path: same schema id, then field-by-field comparison. There is
no Range-specific equality case.

The value renderer recognizes the Range schema name and prints Elixir-style
range literals. Step `1` renders as `first..last`; every other step renders as
`first..last//step`, including negative steps such as `10..1//-1`.

`Range` implements `Enumerable` in source in
`src/modules/runtime_library/range.fz`. The callbacks lower into protocol-owned
implementation functions such as `Enumerable.Range.reduce/3`; their bodies
destructure `%Range{first: first, last: last, step: step}` at the boundary,
then delegate to small `Range` helpers over scalar `first`/`last`/`step` values
for `reduce/5`, O(1) `count/3`, arithmetic `member?/4`, and `slice/6`'s
Elixir-compatible slicing function.
