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

## Spec-Guided Return ABI

Extern ABI types and Fz-visible specs are separate facts. `ExternDecl::params`
and `ExternDecl::ret` describe the C boundary: `ExternTy::Any` means a scalar
is boxed into an `AnyValueRef` before the call, while integer and float lanes
use raw scalar ABI values.

Declared Fz specs describe what a wrapper promises to its callers. Codegen uses
the declared spec result, instantiated for each registered specialization, when
choosing that function's return ABI. This keeps wrappers like:

```fz
@spec dbg(t) :: t when t: any
fn dbg(x), do: fz_dbg_value(x)
```

correct without a dbg-specific fast path. The body calls
`fz_dbg_value(any) :: any`, so the argument is boxed and the extern result is a
boxed `AnyValueRef`. At the wrapper's `Term::Return`, the instantiated
`dbg(integer) :: integer` ABI makes the normal `CodegenValue` coercion unbox
the `AnyRef` result with `fz_unbox_int`.

Do not infer value identity from a repeated type variable. `fn f(t) :: t` means
"same type", not "same value". Boundary correctness should come from marshal
types plus spec-guided coercion.

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

## Resource Typing

`make_resource(payload, dtor)` is typed by the declared runtime spec, not by the
low-level `fz_make_resource` extern return. The extern still returns `any`
because it is the runtime allocation primitive; user-visible call typing
instantiates:

```fz
@spec make_resource(t, (t) -> nil) :: resource(t) when t: integer | cpointer
```

The spec type variable is bound from the payload argument. The `when` bound
keeps resource payloads to raw host handles for now: integers and future
`cpointer` values.

`resource(T)` is a real type constructor. It carries `T` through substitution,
so `make_resource(42, &close/1)` returns `resource(integer)`. If that call is
made inside the lexical owner of:

```fz
@type t :: opaque resource(integer)
```

the typer may mint the nominal `Module::t` result. Continuations and generated
case/if helpers carry the same owner module as the source function so resource
construction inside a module keeps the opaque handle type through CPS lowering.

Do not make plain `resource(integer)` globally interchangeable with every
`opaque resource(integer)`. The alias remains nominal; only the owning module's
lowered functions should mint that opaque type.
