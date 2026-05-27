# Externs

Use this when changing `extern "C"` parsing, lowering, typing, codegen, or
interpreter behavior.

## Variadic Calls

Variadic syntax is represented in two layers:

- `ExternDecl::variadic` says the declaration's fixed `params` may be followed
  by extra call-site arguments.
- Each `Prim::Extern` argument carries an `ExternMarshal`: fixed params are
  `Fixed`, explicitly ascribed variadic args are `Ascribed`, and un-ascribed
  variadic args start as `Auto`.

Do not resolve `Auto` globally on the IR. `FnTypes` is per specialization, so a
single syntactic call can need different marshal classes in different specs.
`ir_extern_marshal::resolve_module_types` fills `FnTypes::extern_marshals`
with concrete `ExternTy` values keyed by `ExternMarshalSite`.

Automatic variadic defaults are intentionally narrow:

- integer types resolve to `ExternTy::I64`
- float types resolve to `ExternTy::F64`
- binary/string values require explicit `:: binary` or `:: cstring`
- other fz values produce `type/extern-marshal`

Later codegen/interpreter work should consume the per-spec side table rather
than guessing from `ExternMarshal::Auto` at the boundary.
