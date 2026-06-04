# Externs

An `extern "C" fn` declaration is a typed door from fz into a C symbol. The
subsystem decides, per call site, how each fz value crosses that door (its
*marshal class*), how the C result comes back, and which machine actually makes
the call. Four pieces carry that work:

- `ExternDecl` (in `src/fz_ir/mod.rs`) holds the static shape of one door: the C
  `symbol`, the fixed `params` wire types, a `variadic` flag, the return wire
  type `ret`, and `ret_descr` (the Fz-visible return type the planner stamps on
  `Prim::Extern`).
- `ExternTy` is the C wire alphabet: `I64`, `F64`, `Any` (one opaque fz value
  word), `Binary`/`CString` (a `*const u8` into a binary, without/with a
  trailing NUL), and `Unit`/`Never` for returns.
- Each `Prim::Extern` argument is an `ExternArg { var, marshal }` whose
  `ExternMarshal` is `Fixed(ty)` (a declared fixed param), `Ascribed(ty)` (an
  explicit `arg :: ty` at the call), or `Auto` (an un-ascribed variadic argument
  awaiting resolution).
- `SpecPlan::extern_marshals` is the per-specialization side table mapping an
  `ExternMarshalSite { block, stmt_idx, arg_idx }` to a concrete `ExternTy`.

Codegen (`src/ir_codegen/prim.rs`) and the interpreter
(`src/ir_interp/extern_call.rs`) read that side table; they never inspect
`ExternMarshal::Auto` at the call boundary. Variadic calls themselves are made
by fixed-arity runtime dispatchers in `runtime/src/extern_variadic.rs`.

## Extern Arguments Are Borrow-Only

Passing a value to an extern borrows it. The `Prim::Extern` lowering in
`src/ir_codegen/prim.rs` (`lower_extern_generic` / `marshal_extern_arg`) emits
the call and the per-arg marshal, but it never sets list alias bits and never
calls `mark_published_ref_aliased`. The alias/publication marking
(`mark_retained_call_args_as_published`, `src/ir_codegen/support.rs`) runs only
at `Call` / `CallClosure` continuation sites in
`src/ir_codegen/terminator.rs`. So an extern argument stays unaliased and
owned-cons-reusable. An extern that needs a value after it returns must copy it
into storage it owns.

## Resolving Auto Marshal Classes

`ir_extern_marshal::resolve_module_types` walks every specialization's
`Prim::Extern` statements and fills `SpecPlan::extern_marshals`. Resolution is
per specialization on purpose: `SpecPlan` is one specialization's view, and a
single syntactic call can need different marshal classes in different specs, so
there is no one global answer to bake onto the IR.

For each argument the resolver copies `Fixed`/`Ascribed` types straight into the
table (and disjointness-checks an `Ascribed` type against the inferred argument
type). An `Auto` argument on a variadic decl runs `resolve_auto` against the
argument's inferred fz type:

- integer types resolve to `ExternTy::I64`
- float types resolve to `ExternTy::F64`
- a binary/string value is an error: it must be written `:: cstring` (NUL
  pointer) or `:: binary` (raw bytes)
- any other fz type is an error

The defaults are deliberately narrow — only integer and float auto-resolve — so
that pointer-shaped wire types are always spelled out at the call. Every error
is a `codes::TYPE_EXTERN_MARSHAL` diagnostic naming the symbol. An `Auto` on a
*non-variadic* decl is an internal lowering invariant violation and also
reports `TYPE_EXTERN_MARSHAL`.

Walkthrough:

```fz
extern "C" fn libc::printf(fmt :: cstring, ...) :: integer
fn main() do libc::printf("%d", 7) end
```

`"%d"` is the fixed `cstring` param; `7` is an `Auto` variadic argument. The
resolver sees `7 : integer`, writes `I64` at that arg's `ExternMarshalSite`, and
the call boundary reads `I64` from the side table.

## Spec-Guided Return ABI

The C wire return (`ExternDecl::ret`) and the Fz-visible return are separate
facts. `ret` governs what crosses the boundary: `ExternTy::Any` boxes a scalar
into an `AnyValueRef` before the call and reads a boxed word back, while `I64`
and `F64` use raw scalar ABI values.

A wrapper function's own return ABI is the per-spec `effective_returns` type the
planner projects for that specialization. Codegen reads it through
`derive_return_tys` (`src/ir_codegen/driver.rs`), keyed by the spec's
`BodyKey`, and coerces the returned `CodegenValue` at `Term::Return` to match.
Codegen does not re-instantiate the declared `@spec` at the return; the declared
contract reaches a spec only inside the planner, and only for a callable-entry
spec that has no concrete activation (`declared_callable_entry_return_state` in
`src/ir_planner/worklist.rs`).

This is what makes an ordinary wrapper come back correctly:

```fz
@spec dbg(t) :: t when t: any
fn dbg(x), do: fz_dbg_value(x)
```

The body calls `fz_dbg_value(any) :: any`, so the argument is boxed and the
extern result is a boxed `AnyValueRef`. Reached as a named callable (for
example `&dbg/1`) and registered for `integer`, that spec's `effective_returns`
is `integer`, so the `Term::Return` coercion unboxes the `AnyRef` result with
`fz_unbox_int`.

A repeated type variable means "same type", not "same value": `fn f(t) :: t`
does not promise the boundary hands back the same object. Boundary correctness
comes from the marshal class on the way in plus this spec-guided coercion on the
way out.

### Direct `dbg` Is Lowered As Identity

A direct source call `dbg(x)` is special-cased in `src/ir_lower/expr.rs`
(`lower_kernel_dbg_intrinsic`). It lowers to a side-effecting
`Prim::Extern(fz_dbg_value, x :: any)` whose result var is discarded, and the
expression's value is the original `x`. That preserves `dbg(t) :: t` by
construction and avoids a polymorphic `Kernel.dbg/1` call edge — which would
make the planner specialize that wrapper and its continuations once per concrete
argument type. A function reference `&dbg/1` still targets the runtime-library
wrapper, because a callable value needs a stable `FnId`.

## Runtime Variadic Dispatchers

A C-variadic call goes through an exported helper in
`runtime/src/extern_variadic.rs` rather than being emitted at the backend call
site. Helper names are mechanical:

```text
fz_call_var_<ret>_<fixed...>_<var...>_to_<ret>
```

Each token is the fz marshal class at the boundary, not necessarily the exact C
parameter type after ABI casts. The helper body owns the target C cast — for
example the `open(path, flags, mode)` dispatcher casts fz integer lanes to
`c_int`/`c_uint` before calling the real variadic function.

The indirection exists because Cranelift exposes a fixed `Signature` of
`AbiParam`s and no variadic fixed-count marker for a call. Emitting `open` as a
plain fixed-arity C call is not ABI-correct on platforms where variadic calls
change register classification. So the backend selects a concrete dispatcher by
the call's resolved marshal shape (`variadic_dispatcher` in `prim.rs`,
`call_variadic_extern` in `extern_call.rs`). An unsupported `(ret, fixed,
variadic)` shape is a compiler/interpreter error that lists the concrete
`ExternTy`s.

`fz_extern_symbol_addr(name)` resolves `dlsym(RTLD_DEFAULT, name)` and caches
both hits and misses by symbol bytes. It returns `0` for a null or unresolved
symbol; callers treat zero as lookup failure, not as a callable pointer. A
dispatcher handed a null function pointer aborts the process.

The three execution paths select dispatchers from the same resolved marshal
shapes. JIT and `ir_interp` resolve symbols at run time through
`fz_extern_symbol_addr`. AOT reaches the same exported runtime symbols through
the staticlib link path: `src/aot_link.rs` (`resolve_runtime_archive`) owns
which `fz-runtime` archive `fz build` links. An ordinary compiler build links
the sibling `libfz_runtime*.a` (`RuntimeArchiveSource::Sibling`); a
coverage-instrumented build instead builds and links a clean isolated archive
under `target/fz-aot-clean-runtime` (`IsolatedCoverageBuild`) so the AOT
executable does not inherit LLVM profile-runtime symbols; an explicit
`FZ_AOT_RUNTIME_STATICLIB` overrides both (`EnvOverride`). Linking emits the
`fz.build.linking` event with `runtime_archive` and `runtime_archive_source`.

## Resource Typing

`make_resource(payload, dtor)` is the `Kernel` wrapper (`kernel.fz`) around the
`fz_make_resource` extern. Both carry the same declared signature, so the
resource type flows from the boundary:

```fz
extern "C" fn fz_make_resource(t, (t) -> nil) :: resource(t) when t: integer | cpointer
@spec make_resource(t, (t) -> nil) :: resource(t) when t: integer | cpointer
```

The type variable binds from the payload argument, and the `when` bound keeps
payloads to raw host handles: `integer` and `cpointer`.

`resource(T)` is a real type constructor (`Types::resource`). It carries `T`
through substitution, so `make_resource(42, &close/1)` types as
`resource(integer)`. When that call sits in the lexical owner of an opaque alias:

```fz
@type t :: opaque resource(integer)
```

the planner mints the nominal `Module::t` result via
`mint_owned_resource_aliases(ty, owner, opaque_inners)`
(`src/types/concrete_types/mod.rs`, called from `src/ir_planner/type_fn.rs` and
`worklist.rs`). The owner is the function's module. Continuations and generated
case/if helpers inherit `owner_module` from `ctx.current_owner_module` during
lowering (`src/ir_lower/cps.rs`), so resource construction keeps the opaque
handle type through CPS lowering rather than decaying to the bare
`resource(integer)`.

The alias is nominal: two opaques with different names are lattice-disjoint, so
a plain `resource(integer)` is not interchangeable with an
`opaque resource(integer)`. Only the owning module's lowered functions mint that
opaque type.
