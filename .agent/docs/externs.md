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

## Runtime Variadic Dispatchers

Runtime C-variadic calls go through `runtime/src/extern_variadic.rs` instead of
being emitted directly at each backend call site. The exported helper names are
mechanical:

```text
fz_call_var_<ret>_<fixed...>_<var...>_to_<ret>
```

The tokens are fz marshal classes at the boundary. The helper body owns the
target C ABI cast, such as the `open(path, flags, mode)` dispatcher casting fz
integer lanes to `c_int`/`c_uint` before calling the real variadic function.

This indirection is intentional. Cranelift 0.131 exposes a fixed `Signature`
made of `AbiParam`s; it does not expose the target ABI's variadic fixed-count
marker for a call. Emitting a direct call to `open(path, flags, mode)` as a
normal fixed-arity C call is not ABI-correct on platforms where variadic calls
change register classification. Keep backend code selecting concrete runtime
dispatchers until Cranelift has a first-class variadic call API.

`fz_extern_symbol_addr(name)` resolves `dlsym(RTLD_DEFAULT, name)` and caches
both hits and misses. It returns `0` for null or unresolved symbols; callers
must treat zero as lookup failure, not as a callable function pointer.

JIT, AOT, and `ir_interp` all select dispatchers from the same resolved marshal
shapes. AOT reaches the same exported runtime symbols through the staticlib link
path. Unsupported shapes must return a compiler/interpreter error that includes
the concrete fixed/variadic `ExternTy` list.
