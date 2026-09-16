# Externs

An `extern` declaration is a typed door from fz into a native symbol. The
subsystem decides, per call site, how each fz value crosses that door (its
*marshal class*), how the C result comes back, and which machine makes the call.
The shapes live in `src/fz_ir`, are shared by both compilers, and are paired with
the runtime FFI helpers that actually call out.

The pieces:

- `ExternDecl` (`src/fz_ir/mod.rs`) — the static shape of one door: the
  `symbol`, fixed `params` wire types, a `variadic` flag, the structural
  `ExternReturn`, and the `abi`.
- `ExternAbi` (`src/fz_ir/mod.rs`) — `C` or `Fz` (below).
- `ExternTy` — the C wire alphabet (below).
- `ExternMarshal` — a per-argument decision: `Fixed(ty)` (a declared param) or
  `Auto` (an un-ascribed variadic argument awaiting resolution; an `arg :: ty`
  ascription at the call resolves it to a concrete `ExternTy` per site).
- `LoweredExtern { abi, params, ret }` (`src/compiler2/body.rs`) — compiler2's
  lowered form: a `LoweredBody::Extern` carries the `ExternAbi`, the param wire
  types, and the return wire type, and lowering also computes the fz-visible
  return type from the declared return.

## Two ABIs

The string in the declaration names the calling convention, and it is parsed
into `ExternAbi` when the extern is lowered. Only two names exist; anything
else is a `lower/unsupported` error, never a silent fall back:

```fz
extern "C"  defp libc::close(c_int) :: c_int                # a plain C symbol
extern "fz" defp fz_binary_concat(binary, binary) :: binary # an fz runtime helper
```

An extern declaration must use `defp`. It binds as an ordinary private function
in its module's lexical namespace and is absent from `ModuleInterface`; a public
API exposes a documented, specified source wrapper instead. For example,
`Kernel.<>/2` is public source while its body alone can call the private
`fz_binary_concat/2` declaration. The resulting quoted extern node and every
downstream ABI/marshalling stage use one source spelling.

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
allocating primitive is a Rust function and a declaration. There is no lowering
function to write, no interpreter match arm to add, and no address table on
either door.

Neither door needs one because the compiler's executables export their symbols
dynamically. `build.rs` passes `-Wl,-export_dynamic` on macOS and `-rdynamic`
elsewhere to the binaries and test binaries, exactly as `aot_link.rs` already
does for an AOT binary's own link line. Without it a linker drops a
`#[unsafe(no_mangle)]` runtime function that no Rust code calls — compiled fz
code names it by symbol, not by Rust path — and it is then not in the process
for `dlsym` to find. With it, `fz_extern_symbol_addr` finds fz's own exports
the same way it finds `sqrt`. The arithmetic and comparison exports stay
reachable for interpreter execution, JIT resolution, and AOT linking. Not
exporting by default is what made
`fz_bitstring_is_binary` resolve on macOS and die on Linux with
`can't resolve symbol` while the whole six-target local gate was green.

There is no variadic form of the `fz` ABI: a variadic call's parameter list is
built per call site from the C rules alone, which leaves nowhere to put the
implicit process argument. The combination is refused at the declaration rather
than in each door's lowering.

### A foreign symbol has to be in the process to be found

`fz_extern_symbol_addr` (`runtime/src/symbol_lookup.rs`) is the ONE resolver for
a symbol, fz's own exports included, and every runtime door goes through it: the
interpreter's `resolve_symbol` and its variadic path call it, and the JIT is
built with it as its `symbol_lookup_fn` rather than cranelift's own `dlsym`.
That matters because the question had THREE answers, each a separate
`dlsym(RTLD_DEFAULT, ..)`, and they disagreed one at a time: teaching the
resolver to open libm fixed the variadic path, routing the JIT through it fixed
`run`, and `resolve_symbol`'s own raw dlsym kept `interp` failing after both.

It tries `dlsym(RTLD_DEFAULT, ..)` first, which searches the loaded global
scope, and then a fixed list of standard C libraries it opens itself
(`STANDARD_C_LIBRARIES`). The list exists because the scope is not enough: on
macOS the C library and the math library are one thing (libSystem) that every
process already has, while elsewhere libm is separate and nothing references
it, so `--as-needed` drops it and `extern "C" defp libc::sqrt(float) :: float`
fails with `dlsym: symbol sqrt not found` on Linux while passing on macOS
(fz-5xp.59).

Opening the libraries rather than arranging a link-time dependency is
deliberate: it does not depend on whether the linker decided to keep one.

The AOT door has the same split on the link line: `aot_link.rs` passes
`-lm -rdynamic` off macOS, where the mac branch passes
`-Wl,-undefined,dynamic_lookup` instead.

Both the library list and that `-lm` are stand-ins for something fz cannot say:
which library a declaration comes from. `libc::` is an fz module
path, not a library name. It works only because every foreign symbol fz names
today is in the C standard library.

A symbol that resolves only on the development platform is the recurring shape
here — see the JIT symbol table above.

## Comparison exports are ordinary calls

`<`, `<=`, `>`, `>=`, `==`, `!=`, `===` and `!==` are ordinary `Kernel`
functions, and each is a typed clause family whose clause bodies call the
matching `fz_op_*` extern declaration. Every one of them carries the four
numeric pairs — integer/integer, float/float, integer/float, float/integer —
on raw `extern "C"` lanes, so comparing two unboxed numbers boxes neither;
mixed-pair identity is answered in source, since an integer is never the same
value as a float. All of them are total, so each also keeps a trailing
`any`/`any` clause: equality and identity call the ref-carrying `fz_op_eq`,
`fz_op_neq`, `fz_op_identical` or `fz_op_not_identical`, and an ordering calls
`Kernel.compare/2`, whose `fz_value_cmp_ref` answers by the total term order.
The orderings' `binary`/`binary` clauses are commented out in `Kernel`, because
the runtime test a `binary` clause compiles to proves only "bitstring" and
cannot be seated ahead of a catch-all; the `fz_op_lt_bb`, `fz_op_lte_bb`,
`fz_op_gt_bb` and `fz_op_gte_bb` declarations they call stay, so restoring a
clause is the uncomment.

Every one of those declarations crosses its door the same way every other
declaration does: `lower_extern_generic` on the native doors, the ordinary FFI
path under the interpreter. Arithmetic already worked this way, and comparison
now does too — no door recognizes a comparison export by name or replaces the
call with an instruction.

## The `fz` ABI is reserved to the runtime library

A declaration outside the bootstrap may not name it. Both things the
convention carries belong to the runtime and to nothing else: the current
`*mut Process`, passed ahead of every declared argument, and fz's internal
value representation, which is what a `binary` or `cstring` parameter arrives
as. A foreign function accepts neither, so a foreign declaration of `"fz"` is
refused. `resolve_extern_abi` raises that in the shared front end, which is the
only place a refusal reaches every door identically.

A variadic `extern "fz"` is refused for a related reason: a variadic call's
parameter list follows the C rules, which leave nowhere to put the process.

Both checks are DEMAND-GATED. An extern that is declared and never called is
never lowered, so neither fires — the declaration compiles silently.

### The declaration is the authority

An `extern` declaration says how its symbol is called: the convention, the
parameter lanes, the result lane. Nothing second-guesses it, for a
runtime-owned symbol any more than for `libc::close`. The proof that a library
declaration is right is that fixtures call it on all three doors, where a wrong
lane shows up as a wrong answer or a crash. A declaration that lies about a
symbol is a wrong C prototype and is treated as one.

Kernel's returning process operations are ordinary private extern declarations.
`fz_self`, `fz_send`, `fz_spawn` and `fz_make_resource` declare the `fz` ABI,
which supplies the current process before their source-visible arguments;
`fz_make_ref` declares the plain `C` ABI. Their source and physical export names
match, and every execution door follows the declaration rather than claiming
those names in compiler lowering. `spawn/1` is the only process-spawn surface;
there is no heap-hint variant or compatibility export.

`Kernel.panic/1` likewise wraps a private `extern "fz" defp fz_panic(any) ::
never`. Its arbitrary fz value stays borrowed from the current process while
the physical export synchronously reports it through `ExecCtx`. The interpreter
turns that report into an owned pending error before the call returns; native
execution writes the same rendered reason to stderr. It never reuses the
atom-only `Process.exit_fault` field, which belongs to compiler dispatch traps.

## Helpers the code generator calls itself

Some calls in compiled code come from lowering rather than from source: a cons
cell, a frame allocation, a boxed integer. Each helper is an ordinary
`extern "C"` function in the runtime library, and codegen names it by that Rust
function item:

```rust
runtime_call!(body, fz_list_cons_int, [process, head, tail])
```

The item says everything. `stringify!` of the identifier is the linker symbol,
and the item's type is the signature: `CLane` maps each parameter's Rust type to
its register lane and `CRet` maps the result, so `*mut Process`, `u32` and `f64`
travel in I64, I32 and F64 by construction. A parameter type with no lane does
not compile — the same bank invariant the wire alphabet carries for a
declaration, read off Rust types instead. Since the signature comes from the
item, the convention comes from the target module's default
(`Module::make_signature`), which is the platform C ABI.

A helper is declared `Import` on first use in the body that calls it and
memoized there, the way `lower_extern_generic` declares a source-visible extern.
Calling a new helper is one `runtime_call!` and an import of its name. The AOT
`main` reaches `fz_aot_setup` and its neighbours the same way. All of this lives
in `native_codegen/runtime_call.rs`.

A body that can call helpers is a `RuntimeCaller`: it holds the module that
declares the symbol, the builder that emits the call, and the memo. `CodegenFn`
is one, for an fz function; `DispatchBody` (`native_codegen/receive.rs`) is the
other, for the receive-dispatch function, which is emitted straight onto a
`FunctionBuilder` and takes its `Process*` as a parameter rather than reading
the pinned register. Both reach a helper by the same `runtime_call!`.

The bodies codegen emits itself — the four halt-cont bodies, `fz_entry_thunk`,
`fz_main_trampoline`, `fz_drain_dtor_entry` — are not Rust functions, so their
signatures are written out where they are declared, `Local`, as `LocalBodies` in
`native_codegen/driver.rs`. A body fz code enters is `Tail`; a body the host
enters through an `extern "C"` fn pointer — `fz_drain_dtor_entry`, `fz_resume`,
and each receive dispatch fn — is built with `Module::make_signature`, so the
target names its convention just as it does for an imported helper.

## The wire alphabet

```text
I64       proven i64                       F64    proven f64
I32       C `int`: the low 32 bits of an integer register, read as signed
Bool      C `uint64_t`: false=0, true=any nonzero word (never an atom id or C _Bool)
Any       one opaque fz value word         Unit   maps to 0 on return
Binary    under "C": *const u8 to the bytes, no NUL guarantee (caller passes
          length). Under "fz": the tagged value ref.
CString   under "C": *const u8 to the bytes with a guaranteed trailing NUL.
          Under "fz": the tagged value ref.
Never     no return lane; returning is a runtime contract violation
```

One table in `src/extern_contract.rs` names every source spelling of a wire
type. Each row carries the `ExternTy` the spelling means, whether a declared
parameter takes its lane from the spelling (`binary`, `cstring`, `c_int`,
`unit`, `nil`) or from its semantic type through `ty_to_extern_ty` (everything
else, so an alias or a constraint can widen it), and, for a wire-only spelling
the type system has no type for, the semantic spelling the contract is
rewritten to before the type checker sees it: `cstring` to `binary`, `c_int` to
`integer`, `unit` to `nil`.

A wire-only spelling names one lane, and a lane is a whole register, so it
stands only as a whole parameter or result. Written inside a larger type,
`:: {c_int, integer}`, `extern_semantic_contract` refuses the contract with
`ExternContractError::WireSpellingInsideType` before any door resolves it, and
the diagnostic names the spelling and states the rule rather than reporting an
unknown type name. The sentence is built from the spelling table, so a new
wire-only row needs no new message.

The spellings, and what a declaration writes:

```text
integer  float  boolean  atom  any  binary  cstring  c_int  unit  nil  never
```

### A C `int` is narrower than an fz integer

`c_int` is fz `integer` semantically — a parameter accepts one and a result is
one — and 32 bits physically. The width is what the declaration is for:

```fz
extern "C" defp libc::open(path :: cstring, flags :: c_int, ...) :: c_int
```

A C function returning `int` writes only the low half of the integer return
register and says nothing about the upper half. x86-64 glibc leaves that half
zero; arm64 libcs happen to write a full 64-bit value. So a result read as a
whole register is the right answer on one machine and `4294967295` for
`open`'s -1 on another — the same program, two answers, and the fixture that
would catch it passes on the development host. Declaring the width instead
makes each door narrow and widen it:

- the fixed-arity native path reduces a `c_int` argument to `i32` at the call
  and sign-extends a `c_int` result back to `i64`;
- a variadic call's FIXED `c_int` parameter is an `i32` lane, while a `c_int`
  in the variadic TAIL is one whole word, because C promotes a narrower
  integer there; the generated call sign-extends the reduced value back;
- the interpreter's fixed path reads the result through a `-> i32` function
  type, and its variadic trampoline sign-extends before returning the word it
  hands back. An argument still travels as a 64-bit word: SysV and AAPCS64
  both have the callee read an `int` parameter out of the low 32 bits.

A pair return field rides a whole return register, so `c_int` is not one of
the three wire types a fixed scalar-pair result is built from; writing it
there is the misplaced-spelling refusal above.

`behavior/c_int_negative_return` pins both signs on all three doors, and
`compiler2_native_lowering_narrows_c_int_arguments_and_sign_extends_c_int_results`
pins the reduce and the sign extension in the lowered CLIF, which is what the
declaration means on every host rather than on this one.

### Fixed C scalar-pair results

An `extern "C"` result written as a fixed two-field tuple of `integer`,
`float`, and/or `boolean` is a `#[repr(C)]`/C struct returned by value. The
fields stay in their existing tuple transport lanes: the boundary does not
first allocate an fz tuple or turn either field into `Any`. All nine semantic
pairs are supported. The interpreter selects one of four concrete carriers
(word/word, word/float, float/word, float/float) through its existing
argument-shape dispatcher and decodes a boolean field as false for zero and
true for any nonzero word. Source boolean arguments remain canonical 0 or 1.

The full declared pair determines the physical signature even when a caller
ignores a field. x86-64 uses each field's natural integer/SSE return bank. On
Linux and Darwin AArch64 only `{float, float}` uses `[F64, F64]`; every other
pair uses `[I64, I64]`, with float bitcasts at the adapter. The target module's
default call convention is authoritative. Larger/nested aggregates and
aggregate arguments are rejected at the shared extern boundary, as is a field
that is not one of those three wire types.

Compiler2 maps each declared `extern_params` name to its `ExternTy` (an unknown
name defaults to `Any`) and lowers the declared return to `ret` plus the
fz-visible return type.

`Never` is a generic return policy, not a recognized symbol. After any foreign
call declared `Never`, the interpreter first consumes a pending context error
and otherwise reports that the foreign function returned despite its contract.
Native code emits a trap on the corresponding bottom-return path. Thus a
foreign function cannot resume fz code even if its physical implementation
returns, while the interpreter can surface a process error without unwinding or
aborting its compiler host.

## Integers and floats ride different register banks

The C ABI passes integers in one register bank and floats in another, on both
SysV and AAPCS64. So a wire type is not just a width: it names WHICH BANK a
position travels in, and caller and callee must agree per position. This is the
subsystem's load-bearing invariant, and every door used to break it:

```fz
extern "C" defp libc::sqrt(float) :: float
libc::sqrt(9.0)        # 3.0
```

The interpreter handed the argument over as its BITS in the integer bank, where
`sqrt` never looks, then read the answer out of the integer return register,
which still held those same bits — so it returned `9.0`, its own input. Native
labelled the returned f64 a tagged value ref and the consumer unboxed it, which
failed Cranelift verification (fz-5xp.31, fz-5xp.19).

What follows from the invariant:

- `ExternLane::lane` (`native_codegen/repr.rs`) is the one definition of which
  bank a wire type travels in: `F64` is the float register, every other
  value-carrying type is one integer-width word, `Unit` and `Never` have no
  lane at all. It is an extension trait rather than a method on `ExternTy`
  because `fz_ir` is free of cranelift. Every native signature — fixed params,
  scalar return, pair fields — reads the bank from it.
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
- A helper's Rust signature must be its declared wire types. The `fz_op_*`
  arithmetic shims took `u64` and bit-punned floats, which was correct only
  while the dispatcher bit-punned them too; fixing one half broke six fixtures
  until the other half was fixed.

`behavior/extern_float_lanes` pins the bank assignments on all three doors,
including both mixed orders — one alone cannot distinguish a correct table from
one with the two mixed shapes transposed.

## Marshal classes resolve per call site

The `ret` and fixed `params` are fixed by the declaration. A variadic call's
un-ascribed arguments are `Auto` and resolve per call site from the argument's
inferred fz type, into a concrete `ExternTy` at an `ExternMarshalSite`:

```text
integer type   -> I64
float type     -> error: a variadic argument is an integer or a pointer
binary/string  -> error: must be written `:: cstring` (NUL) or `:: binary` (raw bytes)
anything else  -> error
```

An ascription names any spelling in the alphabet, so `:: c_int` says a tail
argument is a C `int` where the callee's format string reads one.

The defaults are deliberately narrow — only an integer auto-resolves — so
pointer-shaped wire types are always spelled out at the call. Resolution is per
specialization, because one syntactic call can need different marshal classes in
different contexts, so there is no single answer baked onto the declaration.

A float is refused whether it is inferred or ascribed `:: float`, because the
generated variadic call cannot carry one (see below). The refusal lives in
`resolve_extern_marshals`, which is the shared front end, so all three doors
refuse the same program with the same message.

```fz
extern "C" defp libc::printf(fmt :: cstring, ...) :: c_int
def main() do libc::printf("%d", 7) end
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
def dbg(x), do: fz_dbg_value(x)
```

The body calls `extern "fz" defp fz_dbg_value(any) :: any`, so the argument is
boxed (the ABI adds the process alongside it, which the wrapper never sees) and the
result is a boxed `AnyValueRef`; reached for an `integer`, the wrapper's return
unboxes that word back to an `i64`. A repeated type variable means "same type",
not "same object" — boundary correctness is the marshal class on the way in plus
this coercion on the way out. The declared bound answers only where the call
pinned nothing, so `t` is whatever the caller passed, the empty list included:
`dbg([])` is typed `[]` and not `any` (`types::arrow_match`, fz-kdt.120).

## Variadic calls

A C variadic function has two argument lists at the machine level: the fixed
prefix, passed like any other C call's arguments, and the variadic tail, whose
placement the platform ABI describes separately so `va_arg` can walk it.
Cranelift cannot express the distinction — a `Signature` is a flat parameter
list with no marker (bytecodealliance/wasmtime#1030) — so fz produces the
placement by choosing the parameter list, in one lowering that every door
reaches: `emit_variadic_c_call` in `native_codegen/variadic.rs`.

With variadic arguments restricted to integer and pointer values:

- on **x86-64 SysV** and **Linux AArch64** a variadic argument goes exactly
  where an ordinary argument of the same type would, so an ordinary call whose
  signature lists the variadic values as extra integer parameters IS the
  variadic call;
- on **Apple AArch64** variadic arguments never use registers: each occupies its
  own 8-byte stack slot starting at the stack pointer. The lowering produces
  that by padding the parameter list with dummy `I64` parameters until all eight
  integer argument registers are spoken for, so every parameter after them is
  assigned to the stack. It is exact, not approximate: an Apple variadic slot is
  8 bytes, a stack integer or pointer parameter is 8 bytes, and both areas begin
  at the stack pointer, so the padded call's overflow area is byte-for-byte the
  variadic area the callee reads. A fixed parameter in the float bank does not
  consume an integer register and is not counted.

The strategy and the measurement behind it come from rustc's own Cranelift
backend, [rustc_codegen_cranelift
#1500](https://github.com/rust-lang/rustc_codegen_cranelift/pull/1500).

The integer-only restriction is what makes one lowering right on all three
targets. A float variadic argument would additionally need the caller to set
x86-64's `%al` to the number of vector registers used, which a generated
ordinary call has no way to say. That is why the marshal front end refuses one.

Each door supplies the callee's address its own way. Native codegen declares the
foreign symbol as an ordinary `Linkage::Import` function — a placeholder
signature nothing calls through — and takes its `func_addr`, so the linker or
the JIT's symbol lookup resolves it like any other extern. The interpreter has
no linker, so it resolves the address through `fz_extern_symbol_addr` and then
calls a generated trampoline: one JIT'd
`extern "C" fn(callee: usize, words: *const u64) -> u64` per call shape, which
loads the marshalled argument words out of the array and reaches the same
lowering. The trampolines and the module holding their code live together on
`IrInterpRuntime`, built on first use and memoized by shape (fixed lanes,
variadic count, result lane). Two parameters is all the trampoline takes, so
`MAX_INTERP_EXTERN_ARGS` never applies to a variadic call.

A variadic call's result is a scalar integer lane; a float-returning variadic
declaration is refused at each door.

## Resource typing

`make_resource(payload, dtor)` is the `Kernel` wrapper around the
`fz_make_resource` extern; both carry the same signature so the resource type
flows from the boundary:

```fz
extern "fz" defp fz_make_resource(t, (t) -> nil) :: resource(t) when t: integer | cpointer
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

`Kernel.claim_resource/1` is the deterministic counterpart to fallback
cleanup. It reads the payload and then atomically claims the shared off-heap
resource, returning `{:ok, payload}` to the one winner or `{:error, :closed}`
to every other alias. A claim is visible through aliases in other processes and
disarms the FZ destructor at final release. The successful caller must perform
cleanup itself. The claim and payload read are one non-yielding runtime-library
operation today; resource users must not expose a raw payload to application
code before they own it.

## Proof gates

```text
cargo test --test fixture_matrix file_handle      # resource lifecycle + dtor
cargo test --test fixture_matrix file_resource_lifecycle
cargo test --test fixture_matrix resource_claim   # cross-process one-shot claim
cargo test --lib compiler2_unknown_extern_abi_is_a_lower_diagnostic
cargo test --lib compiler2_fz_abi_is_reserved_to_the_runtime_library
cargo test --lib compiler2_variadic_extern_too_few_args_is_a_lower_diagnostic
cargo test --test fixture_matrix extern_float_lanes   # register banks, 3 doors
cargo test --test fixture_matrix c_int_negative_return    # C int width, 3 doors
cargo test --lib compiler2_native_lowering_narrows_c_int_arguments_and_sign_extends_c_int_results
cargo test --test fixture_matrix variadic_three_integers  # variadic ABI, 3 doors
cargo test --test aot_variadic_open                   # variadic call through the linker
```
