# Externs

An `extern` declaration is a typed door from fz into a native symbol. The
subsystem decides, per call site, how each fz value crosses that door (its
*marshal class*), how the C result comes back, and which machine makes the call.
The shapes live in `src/fz_ir`, are shared by both compilers, and are paired with
the runtime FFI helpers that actually call out.

The pieces:

- `ExternDecl` (`src/fz_ir/mod.rs`) — the static shape of one door: the
  `symbol`, fixed `params` wire types, a `variadic` flag, the return wire type
  `ret`, and the `abi`.
- `ExternAbi` (`src/fz_ir/mod.rs`) — `C` or `Fz` (below).
- `ExternTy` — the C wire alphabet (below).
- `ExternMarshal` — a per-argument decision: `Fixed(ty)` (a declared param),
  `Ascribed(ty)` (`arg :: ty` at the call), or `Auto` (an un-ascribed variadic
  argument awaiting resolution).
- `LoweredExtern { abi, params, ret }` (`src/compiler2/body.rs`) — compiler2's
  lowered form: a `LoweredBody::Extern` carries the `ExternAbi`, the param wire
  types, and the return wire type, and lowering also computes the fz-visible
  return type from the declared return.

## Two ABIs

The string in the declaration names the calling convention, and it is parsed
into `ExternAbi` when the extern is lowered. Only two names exist; anything
else is a `lower/unsupported` error, never a silent fall back:

```fz
extern "C"  fn libc::close(integer) :: integer            # a plain C symbol
extern "fz" fn fz_binary_concat(binary, binary) :: binary # an fz runtime helper
```

The ABI decides two things at once.

**The implicit process argument.** An `extern "fz"` symbol receives the current
`*mut Process` as an implicit first argument, ahead of every declared one.
Anything that allocates on the process heap needs it, which is every
interesting String, IO and number-formatting primitive. `extern "C"` receives
exactly the declared arguments.

**What `binary` and `cstring` mean.** A C function taking either wants a
`*const u8` into the bytes (`cstring` additionally guarantees a trailing NUL).
An fz runtime helper taking either wants the tagged value ref it works in,
because it operates in fz's own representation and may allocate a new value.
Same declared types, two conventions — which is why the ABI has to reach the
marshalling code rather than being consumed at the front door. `integer` and
`float` are unaffected BY THE ABI: they are raw scalars under both. They are
not interchangeable, though — see the register banks below.

Both doors read the same property from the same declaration
(`prim.rs::lower_extern_generic` and `ir_interp/extern_call.rs`), so adding an
allocating primitive is a Rust function, a declaration, a row in
`extern_contract.rs::RUNTIME_SYMBOLS`, and an address for each door that needs
one: `ir_codegen/backend.rs::runtime_symbol_addrs` for the JIT, and
`ir_interp/extern_call.rs::resolve_symbol` for the interpreter, which cannot
rely on dlsym reaching a statically-linked rlib. AOT needs no address row for a
runtime-crate export, which is `#[unsafe(no_mangle)]` and reachable through the
staticlib link. There is no lowering function to write and no interpreter match
arm to add.

The JIT's addresses are a table, so tests can enumerate them.
`every_declared_runtime_symbol_is_reachable_from_compiled_code` requires every
owned extern symbol to have a registered native address. Intrinsics have a
separate typed declaration and never enter this symbol inventory; see
[`intrinsics`](intrinsics.md).

There is no variadic form of the `fz` ABI: every variadic call goes through a
fixed-arity C dispatcher, which has nowhere to put the implicit process
argument. The combination is refused at the declaration rather than in each
door's lowering.

### A foreign symbol has to be in the process to be found

`fz_extern_symbol_addr` is the ONE resolver for a foreign symbol, and every
runtime door goes through it: the interpreter's `resolve_symbol` fallback and
its variadic path call it, and the JIT is built with it as its
`symbol_lookup_fn` rather than cranelift's own `dlsym`. That matters because
the question had THREE answers, each a separate `dlsym(RTLD_DEFAULT, ..)`, and
they disagreed one at a time: teaching the resolver to open libm fixed the
variadic path, routing the JIT through it fixed `run`, and `resolve_symbol`'s
own raw dlsym kept `interp` failing after both.

It tries `dlsym(RTLD_DEFAULT, ..)` first, which searches the loaded global
scope, and then a fixed list of standard C libraries it opens itself
(`STANDARD_C_LIBRARIES`). The list exists because the scope is not enough: on
macOS the C library and the math library are one thing (libSystem) that every
process already has, while elsewhere libm is separate and nothing references
it, so `--as-needed` drops it and `extern "C" fn libc::sqrt(float) :: float`
fails with `dlsym: symbol sqrt not found` on Linux while passing on macOS
(fz-5xp.59).

Opening the libraries rather than arranging a link-time dependency is
deliberate: it does not depend on whether the linker decided to keep one.

The AOT door has the same split on the link line: `aot_link.rs` passes
`-lm -rdynamic` off macOS, where the mac branch passes
`-Wl,-undefined,dynamic_lookup` instead.

Both the library list and that `-lm` are stand-ins for something fz cannot say:
which library a declaration comes from (fz-5xp.61). `libc::` is an fz module
path, not a library name. It works only because every foreign symbol fz names
today is in the C standard library.

A symbol that resolves only on the development platform is the recurring shape
here — see the JIT symbol table above.

## The `fz` ABI is reserved to the runtime library

Only compiler-owned bootstrap code may declare the `fz` ABI, because it
passes a running process and fz's internal value representation.
The declaration's stored `FunctionSource.owner: SourceOwner` establishes that
provenance;
quoted span metadata never grants bootstrap privilege.
`resolve_extern_abi` checks this boundary, rejects unknown ABIs and variadic
`fz` declarations, and compares owned runtime symbols against
`extern_contract.rs::RUNTIME_SYMBOLS`. The interpreter's address book checks
the same declared convention before performing a native call.

These checks are demand-gated: an uncalled declaration is not lowered.

Compiler/runtime operations use `intrinsic` declarations. The arithmetic and
comparison families and seven process primitives carry an `Intrinsic`
identity through lowering; their source declarations contain no foreign ABI.
A same-spelled ordinary function keeps its own body. The generic extern path
accepts only `LoweredExtern` and performs no intrinsic symbol interception.

Some runtime functions implement intrinsic lowerings while remaining real
exports. `fz_panic`, for example, receives `(*mut Process, u64)`, so its
owned-symbol record has the `Fz` ABI even though the Kernel declaration is an
intrinsic. Declaring that export as `extern "C"` is refused.

## The wire alphabet

```text
I64       proven i64                       F64    proven f64
Any       one opaque fz value word         Unit   maps to 0 on return
Binary    under "C": *const u8 to the bytes, no NUL guarantee (caller passes
          length). Under "fz": the tagged value ref.
CString   under "C": *const u8 to the bytes with a guaranteed trailing NUL.
          Under "fz": the tagged value ref.
Never     diverges
```

Compiler2 maps each declared `extern_params` name to its `ExternTy` (an unknown
name defaults to `Any`) and lowers the declared return to `ret` plus the
fz-visible return type.

## Integers and floats ride different register banks

The C ABI passes integers in one register bank and floats in another, on both
SysV and AAPCS64. So a wire type is not just a width: it names WHICH BANK a
position travels in, and caller and callee must agree per position. This is the
subsystem's load-bearing invariant, and every door used to break it:

```fz
extern "C" fn libc::sqrt(float) :: float
libc::sqrt(9.0)        # 3.0
```

The interpreter handed the argument over as its BITS in the integer bank, where
`sqrt` never looks, then read the answer out of the integer return register,
which still held those same bits — so it returned `9.0`, its own input. Native
labelled the returned f64 a tagged value ref and the consumer unboxed it, which
failed Cranelift verification (fz-5xp.31, fz-5xp.19).

What follows from the invariant:

- `lower_extern_generic` gives `F64` its own `LowerOut::RawF64` lane, and the
  return match is exhaustive on purpose. A wildcard there is what let `F64`
  default into the `ValueRef` arm in the first place.
- The interpreter cannot transmute an address by arity alone. `ArgWord` tags
  each argument with its bank, and `dispatch_shapes!` enumerates every SHAPE —
  an arity times an assignment of its parameters to the two banks, 31 in all —
  instantiated once per return lane.
- `MAX_INTERP_EXTERN_ARGS` (4) is a ceiling the backend does not have, so a
  5-parameter extern is refused under `interp` and runs under `run`/`build`
  (fz-5xp.32). An `extern "fz"` spends one slot on the implicit process word.
- A helper's Rust signature must use its declared wire types. Arithmetic
  intrinsics carry their own typed lane descriptor and bypass the C dispatcher.

`behavior/extern_float_lanes` pins the bank assignments on all three doors,
including both mixed orders — one alone cannot distinguish a correct table from
one with the two mixed shapes transposed.

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

## Wire return vs fz-visible return

Note: "fz-visible" here means the TYPE fz code sees, unrelated to the `"fz"`
calling convention above.

These are separate facts. `ret` governs what crosses the boundary: `Any` boxes a
scalar into an `AnyValueRef` before the call and reads a boxed word back, while
`I64`/`F64` use raw scalar ABI values. The function's *fz-visible* return is its
inferred return type, and a wrapper coerces the boxed result to match. That is
what makes an ordinary wrapper come back correctly:

```fz
@spec dbg(t) :: t when t: any
fn dbg(x), do: fz_dbg_value(x)
```

The body calls `extern "fz" fn fz_dbg_value(any) :: any`, so the argument is
boxed (the ABI adds the process alongside it, which the wrapper never sees) and the
result is a boxed `AnyValueRef`; reached for an `integer`, the wrapper's return
unboxes that word back to an `i64`. A repeated type variable means "same type",
not "same object" — boundary correctness is the marshal class on the way in plus
this coercion on the way out. The declared bound answers only where the call
pinned nothing, so `t` is whatever the caller passed, the empty list included:
`dbg([])` is typed `[]` and not `any` (`types::arrow_match`, fz-kdt.120).

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
`fz_make_resource` intrinsic; both carry the same signature so the resource type
flows from the boundary:

```fz
intrinsic "make_resource" fn fz_make_resource(t, (t) -> nil) :: resource(t) when t: integer | cpointer
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

Inside the owning module, `.value` on a resource handle projects the payload.
Lowering keeps this as ordinary field access, and both backend interpreter and
native/JIT/AOT paths read it through the shared named-field runtime ABI.

## Proof gates

```text
cargo test --test fixture_matrix file_handle      # resource lifecycle + dtor
cargo test --test fixture_matrix file_resource_lifecycle
cargo test --lib address_book_test                # convention <-> address
cargo test --lib compiler2_unknown_extern_abi_is_a_lower_diagnostic
cargo test --lib compiler2_fz_abi_is_reserved_to_the_runtime_library
cargo test --lib compiler2_refuses_a_runtime_symbol_declared_with_the_wrong_abi
cargo test --lib compiler2_variadic_extern_too_few_args_is_a_lower_diagnostic
cargo test --test fixture_matrix extern_float_lanes   # register banks, 3 doors
```
