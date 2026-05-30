# Range

fz represents `Range` as a normal schema-backed Struct. It does not have a
dedicated heap tag. The canonical schema is registered lazily through
`SchemaRegistry::range()` and has three raw signed-integer fields:

- offset 0: `first`
- offset 8: `last`
- offset 16: `step`

`Heap::alloc_range(first, last, step)` is the runtime constructor. It asserts
that `step != 0`, allocates a Struct with the canonical Range schema, writes the
three raw fields, and returns a `TAG_STRUCT` `AnyValueRef`. The C ABI entrypoint
is `fz_range_new(process, first, last, step)`, where the three values are
integer `AnyValueRef` words. `Kernel.range/3` is the fz wrapper used by surface
desugaring and fixtures.

Because Range is an ordinary Struct, runtime equality follows the existing
struct equality path: same schema id, then field-by-field comparison. There is
no Range-specific equality case.

The value renderer recognizes the Range schema name and prints Elixir-style
range literals. Step `1` renders as `first..last`; every other step renders as
`first..last//step`, including negative steps such as `10..1//-1`.
