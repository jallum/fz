# Externs

An `extern "C" fn` declaration is a typed door from fz into a C symbol. The
subsystem decides, per call site, how each fz value crosses that door (its
*marshal class*), how the C result comes back, and which machine makes the call.
The shapes live in `src/fz_ir`, are shared by both compilers, and are paired with
the runtime FFI helpers that actually call out.

The pieces:

- `ExternDecl` (`src/fz_ir/mod.rs`) — the static shape of one door: the C
  `symbol`, fixed `params` wire types, a `variadic` flag, and the return wire
  type `ret`.
- `ExternTy` — the C wire alphabet (below).
- `ExternMarshal` — a per-argument decision: `Fixed(ty)` (a declared param),
  `Ascribed(ty)` (`arg :: ty` at the call), or `Auto` (an un-ascribed variadic
  argument awaiting resolution).
- `LoweredExtern { abi, params, ret }` (`src/compiler2/body.rs`) — compiler2's
  lowered form: a `LoweredBody::Extern` carries the abi, the param wire types,
  and the return wire type, and lowering also computes the fz-visible return type
  from the declared return.

## The wire alphabet

```text
I64       proven i64                       F64    proven f64
Any       one opaque fz value word         Unit   maps to 0 on return
Binary    *const u8 to a binary's bytes, no NUL guarantee (caller passes length)
CString   *const u8 to a binary's bytes with a guaranteed trailing NUL
Never     diverges
```

Compiler2 maps each declared `extern_params` name to its `ExternTy` (an unknown
name defaults to `Any`) and lowers the declared return to `ret` plus the
fz-visible return type.

## Marshal classes resolve per call site

The `ret` and fixed `params` are fixed by the declaration. A variadic call's
un-ascribed arguments are `Auto` and resolve per call site from the argument's
inferred fz type, into a concrete `ExternTy` at an `ExternMarshalSite`:

```text
integer type   -> I64
float type     -> F64
binary/string  -> error: must be written `:: cstring` (NUL) or `:: binary` (raw bytes)
anything else  -> error
```

The defaults are deliberately narrow — only integer and float auto-resolve — so
pointer-shaped wire types are always spelled out at the call. Resolution is per
specialization, because one syntactic call can need different marshal classes in
different contexts, so there is no single answer baked onto the declaration.

```fz
extern "C" fn libc::printf(fmt :: cstring, ...) :: integer
fn main() do libc::printf("%d", 7) end
```

`"%d"` is the fixed `cstring` param; `7` is an `Auto` variadic argument that
resolves to `I64`, and the call boundary reads `I64` from the resolved marshal.

## Extern arguments are borrow-only

Passing a value to an extern **borrows** it: extern argument lowering never sets
a list alias bit and never marks a value published (see the alias-bit model in
[`any-value`](any-value.md)). So an extern argument stays unaliased and
owned-cons-reusable. An extern that needs a value after it returns must copy it
into storage it owns.

## C wire return vs fz-visible return

These are separate facts. `ret` governs what crosses the boundary: `Any` boxes a
scalar into an `AnyValueRef` before the call and reads a boxed word back, while
`I64`/`F64` use raw scalar ABI values. The function's *fz-visible* return is its
inferred return type, and a wrapper coerces the boxed result to match. That is
what makes an ordinary wrapper come back correctly:

```fz
@spec dbg(t) :: t when t: any
fn dbg(x), do: fz_dbg_value(x)
```

The body calls `fz_dbg_value(any) :: any`, so the argument is boxed and the
result is a boxed `AnyValueRef`; reached for an `integer`, the wrapper's return
unboxes that word back to an `i64`. A repeated type variable means "same type",
not "same object" — boundary correctness is the marshal class on the way in plus
this coercion on the way out.

## Runtime variadic dispatchers

A C-variadic call does not emit a backend call directly; it goes through an
exported fixed-arity helper in `runtime/src/extern_variadic.rs`. Helper names are
mechanical — `fz_call_var_<ret>_<fixed...>_<var...>_to_<ret>` — and each token is
the fz marshal class at the boundary; the helper body owns the C cast (e.g.
casting fz integer lanes to `c_int`/`c_uint`). The indirection exists because
Cranelift exposes a fixed `Signature` with no variadic marker, so emitting `open`
as a plain fixed-arity call would not be ABI-correct. The backend (and the
interpreter) select a concrete dispatcher from the call's resolved marshal shape;
an unsupported shape is a diagnostic listing the concrete `ExternTy`s.

`fz_extern_symbol_addr(name)` resolves `dlsym(RTLD_DEFAULT, name)`, caching hits
and misses; it returns `0` for an unresolved symbol (treated as failure, not a
callable pointer). All execution paths share these symbols: the JIT and
interpreter resolve at run time; AOT reaches the same exported runtime symbols
through the staticlib link.

## Resource typing

`make_resource(payload, dtor)` is the `Kernel` wrapper around the
`fz_make_resource` extern; both carry the same signature so the resource type
flows from the boundary:

```fz
extern "C" fn fz_make_resource(t, (t) -> nil) :: resource(t) when t: integer | cpointer
@spec make_resource(t, (t) -> nil) :: resource(t) when t: integer | cpointer
```

`resource(T)` is a real type constructor on the `Types` trait; the variable binds
from the payload, so `make_resource(42, &close/1)` is `resource(integer)`. When
that call sits in a module that declares `@type t :: opaque resource(integer)`,
the planner mints the nominal opaque alias (`mint_owned_resource_aliases`) owned
by that module. The alias is nominal — two opaques with different names are
lattice-disjoint (see [`set-theoretic-types`](set-theoretic-types.md)) — so a
plain `resource(integer)` is not interchangeable with the opaque handle, and only
the owning module's functions mint it.

## Proof gates

```text
cargo test --test fixture_matrix externs
cargo test --test fixture_matrix file_handle      # resource lifecycle + dtor
cargo test --test fixture_matrix file_resource_lifecycle
```
