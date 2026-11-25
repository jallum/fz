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
- `LoweredExtern { abi, symbol, params, variadic, ret }` (`src/compiler2/body.rs`)
  — compiler2's lowered form of the wire ABI. An extern has no body to lower:
  its `FunctionContract` (`jobs/contract.rs::derive_function_contract`) resolves
  the wire ABI once, from the surface declaration, and carries it as
  `extern_wire`. Every wire-ABI reader goes through the contract; there is no
  `LowerFunction` job, and no `LoweredBody`, for an extern.

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

**An fz extern's answer is one scalar or an `any`.** A helper that can fail
returns a tagged list. `fz_unescape_string(binary)`, behind
`Macro.unescape_string/1`, answers `[1, text]` on success and `[0, message]` on
a malformed escape, and the library function raises `ArgumentError` for the
second.

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
exporting by default made a runtime function resolve on macOS and die on Linux
with `can't resolve symbol` while the whole six-target local gate was green.

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
`any`/`any` clause: equality and identity call `fz_op_eq`, `fz_op_neq`,
`fz_op_identical` or `fz_op_not_identical`, and an ordering calls
`Kernel.compare/2`, whose `fz_value_cmp_ref` answers by the total term order.
Each of these takes both operands as `stored_value`, so a number of a kind the
compiler cannot see crosses without a box.
Each of the eight also carries a `binary`/`binary` clause, after its numeric
clauses and before the `any`/`any` clause, guarded by `is_binary` on both
operands. It calls `fz_op_eq_bb`, `fz_op_neq_bb`, `fz_op_lt_bb`,
`fz_op_lte_bb`, `fz_op_gt_bb` or `fz_op_gte_bb`, `extern "fz"` declarations
whose `binary` parameters cross as the binaries' tagged words, the process
first (`binary_bool_export!` in `runtime/src/ir_runtime.rs`). `===` and `!==`
of two binaries are `==` and `!=`, since no numeric widening applies to a
binary, so they call `fz_op_eq_bb` and `fz_op_neq_bb`. Each function decodes
its words with `Bin::of_binary`. Equality is `Bin`'s: the same bit length and
the same bits, whether either side is a view or a literal, and whatever the
padding of a partial last byte. The orderings are `Bin`'s `Ord`, the order
`TermComparator` gives two bitstrings: the bits both hold compare first, and a
prefix comes before what it begins.

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
none`. Its arbitrary fz value stays borrowed from the current process while
the physical export renders its failure line, marks the process failed and
hands the line to the `ExecCtx` fault sink, all before it returns, unless a
`try` handler is on the stack, in which case it delivers the raise there
instead. A `none` extern that returns has raised: native code runs the queued
handler in the call's place or returns to the scheduler when the process
failed (and traps when neither happened), and the interpreter runs its handler
frame or ends the process. See [exceptions](exceptions.md).

`Kernel.inspect/1` wraps a private `extern "fz" defp fz_inspect(stored_value) :: binary`,
which renders with Elixir's default options. `Kernel.inspect/2` wraps
`fz_inspect_with(stored_value, any) :: binary`, whose second argument is the option
keyword list; the physical export reads it for `limit:` (`Limit::from_options`)
before it renders. The two are separate because `inspect/1` must stay a
dispatch-pure helper (guard helpers such as `map_size/1` call it to word their
failure) and must not box an argument: a literal list is not a guard
expression, and a scalar `any` argument allocates a heap box on every call.
The list is checked in fz source (`checked_inspect_options/2` in
`lib/kernel.fz`) and refused there, because only a `none` extern may fail its
process.

## Helpers the code generator calls itself

Some calls in compiled code come from lowering rather than from source: a
boxed integer, the sharing of a list. Each helper is an
ordinary `extern "C"` function in the runtime library, and codegen names it by
that Rust function item:

```rust
runtime_call!(body, fz_mark_published_ref_aliased, [process, head])
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
memoized there by `runtime_call_ref`, the way `extern_call_ref` declares a
source-visible extern. Calling a new helper is one `runtime_call!` and an import
of its name. All of this lives in `native_codegen/runtime_call.rs`.

A body that can call helpers is a `RuntimeCaller`: it holds the module that
declares the symbol, the builder that emits the call (`with_builder`), and the
memo. `CodegenFn` is one, for an fz function; `DispatchBody`
(`native_codegen/receive.rs`) is another, for the receive-dispatch function,
which is emitted straight onto a `FunctionBuilder` and takes its `Process*` as a
parameter rather than reading the pinned register; the AOT `main`
(`ir_codegen/aot_main.rs`), which reaches `fz_aot_setup` and its neighbours, is
the third. All reach a helper by the same `runtime_call!`.

### How a call reaches an import

Every call to an import (a helper, a source-visible extern, an extern a guard
calls) takes its function-local reference from `import_call_ref`
(`native_codegen/clif.rs`). Where the code will run is a `CodeHome`, fixed when
the ISA is built (`host_isa_for`):

- `Executable`: the object is linked with the runtime archive, so the linker
  places every import within a direct branch's reach, adding a stub or PLT entry
  for a C library function. The ISA sets `is_pic` and `use_colocated_libcalls`,
  `import_call_ref` marks the reference colocated, and the call is one `bl`
  (`call rel32` on x86-64). Cranelift's own library calls follow the same flag.
- `ThisProcess`: JIT code lives in its own arena, which may lie beyond a direct
  branch's ±128 MiB reach of the runtime in the process image. The reference is
  not colocated, so the call loads its callee's address and branches through a
  register.

Only calls take the near reference. A near address is pc-relative and cannot
name a function in a shared library, so taking an extern's address (the variadic
path below) declares it afresh: `CodegenCache` keeps `extern_calls` and
`extern_addrs` apart.

### Inline recipes

`native_codegen/recipe.rs` holds one table, `RECIPES`. A row names a runtime
function by its Rust item and emits Cranelift instructions that compute what
that function computes. Both ways compiled code reaches a runtime function ask
the table first, keyed by the function's symbol: `call_runtime1` /
`call_runtime_condition` (`runtime_call1!`, `runtime_condition!`, for the
helpers codegen calls itself, on `CodegenFn` and `DispatchBody` alike) and the
lowering of an `extern "C" defp` declaration (`lower_extern_generic`,
`lower_extern_pair`, keyed by `decl.symbol`). A row emits its instructions and
declares no import; a symbol with no row, or a row that declines the instance,
emits the call.

A row answers in one of three shapes (`Emitted`) and no others:

- `Value`: one word or float, in the lane the function returns.
- `Condition`: an `I8` the next branch uses directly. It is a
  `CodegenValue::Condition` when every use of the variable is a branch
  (`if_only_conds`), the atom boolean otherwise (`condition_value`).
- `Checked`: a value and the `I8` condition that says it failed, in place of
  the C scalar pair. The failed field is bound the same way a `Condition` is,
  and the same holds for a checked extern that has no row: the pair's boolean
  field reaches the branch as a condition (`decode_foreign_boolean_word`).

A recipe does not validate its argument: the Rust function panics on a
malformed word, the instructions read whatever the word says.

`fz_bitstring_byte_extent` and `fz_bitstring_bit_extent` (`byte_size` and
`bit_size` of a proven binary, and of a cursor's rest) are `Value` rows. The
header word is word 0 of both binary forms, so they read it at the word's
address without testing the form, take its bit length (the bits below the
shared mark, above the low nibble: `BITSTRING_HEADER_LEN_MASK`,
`BITSTRING_BIT_LEN_SHIFT`), and subtract the bit position; the byte row then
rounds up to whole bytes.

The six `fz_op_*_bb` functions (`==`, `!=`, `<`, `<=`, `>` and `>=` of two
binaries) are `Emit::BinaryCompare` rows, `Condition` rows that may call the
runtime, so a call site asks `emit_in_body(body, symbol, args)` (it answers
every in-place row, and `emit_inline` panics for these). Their arguments are
the process, then the two tagged words, as the `fz` extern passes them, and
`lower_extern_generic` offers a process-taking extern to the table with the
process first. `native_codegen/binary_compare.rs` emits them: the same word is
one binary, which equals itself, so the row answers `true` for `==`, `<=` and
`>=` and `false` for the others. For `==` and `!=` the two header words are
then xor-ed and masked with `BITSTRING_HEADER_LEN_MASK`, and different bit
lengths answer without a call. Every other pair reaches the cold block that
calls the row's own function and takes its word as the condition. The ordering
rows have only the same-word test, since bit lengths do not settle an order.
`lower_eq_binop` takes the same instructions for two operands typed as
bitstrings under `==`, `!=`, `===` and `!==`, and `lower_cmp_binop` for
`<`, `<=`, `>` and `>=`. A receive guard's comparison of two values it cannot
type tests both kinds and takes them for two binaries
(`emit_comparison_of_refs`), `fz_value_eq_widening_ref`, `fz_value_eq_ref` or
`fz_value_cmp_ref` otherwise. A guard may call these functions: an `fz`
extern's `binary` parameter is admitted to `GuardExtern`, and all three guard
evaluators pass the tagged word. The interpreter's `interp_operator_eq` and
`interp_value_eq` call `fz_op_eq_bb`, and `interp_cmp` orders with `Bin::cmp`,
for two binaries before the generic comparator. `recipe_test` proves every row
against its function over inline binaries, views, the literal bit, equal and
unequal bytes, prefixes, other lengths and bitstrings that differ only in
their padding bits.

A row that allocates is the other kind of row (`Emit::Cell`, `Emit::Reuse`, `Emit::Struct`,
`Emit::Closure`, `Emit::Box`): it takes the
process as its first argument, as the runtime function does, and writes the
object itself. Asking `emit_inline` for one panics; a call site asks
`emit_cell(body, symbol, args)`, which registers the allocation site in the
body's `SiteScope` (`CodegenFn::scope`, given when the body is made: the
function's display name for a compiled function, the shim's name for a shim).
The four list-cell
rows, `fz_list_cons_int`, `fz_list_cons_float`, `fz_list_cons_atom` and
`fz_list_cons_any`, place the 16-byte cell through `emit_place` (the one inline
bump, see [scheduler zero-arg closures](scheduler-zero-arg-closures.md)) and
write its two words in `native_codegen/list_cell.rs`: the head's payload, and
the link word, the tail's address with the head's kind in the bits a ref word
keeps its kind in. The tail travels as a (word, kind) pair, and an inline row
requires the kind to be the constant `LIST`: native code emits the inline cell
only when the tail's type is within `any_list()`, and calls the runtime entry
otherwise, which places a terminator cell for a tail that is not a list (see
`any-value.md`). A new cell carries no alias bit. A scalar head's kind is a
constant. A ref head is decoded as `AnyValue::from_ref` decodes it (a boxed
int, float or reference is read from its box, any other word is its payload),
and a list or struct head is shared first by a call to
`fz_mark_published_ref_aliased`, the one call a cell makes. The runtime
(`fz_heap_room`) is asked only for room when the tip is full.

A list cell rebuilt from the cell it replaces is decided in place too.
`fz_list_reuse_or_cons_parts` (the head's payload word and a kind constant, then
the tail's word and kind)
and the same function applied to a head given as a ref word (decoded by
`storage_raw` and `tag`; `REUSE_REF_HEAD`) are rows, and a call site asks `emit_reuse(body, symbol, args)`;
`native_codegen/list_reuse.rs` writes them in the runtime function's order. The
attempt is counted in `Process::list_retention_attempts`. A cell whose head
word, head kind and tail already are the new ones is the answer and counts a
hit, with nothing written. Otherwise the head is shared, then a cell the
construction may rewrite (a constant the call site passes) whose alias bit is
clear is rewritten in place and counts a hit, and any other is replaced by a
new cell placed through `emit_place` and written by `list_cell.rs`. The alias
bit is read after the head is shared, because a head that is the source cell
itself marks it. The interpreter calls `fz_list_reuse_or_cons_parts`.

A struct or tuple and a closure are placed the same way, and their rows are
named by the heap method the interpreter calls, as the runtime has no extern
for them: `Heap::alloc_struct_unwritten` (the process, the schema id and the
size) and `Heap::alloc_closure` (the process, the denotation, the arity, the
capture count, the halt kind and the code address). A call site asks
`emit_object(body, symbol, args)`, which reads the arguments after the
process back as constants (a closure's code address stays a value) and
answers the object's address and ref word. `native_codegen/inline_object.rs`
writes the struct's header word, or the closure's header word (denotation,
capture count and halt kind packed in, arity) and its code address; the code
that builds the object stores the fields or captures and their kind bytes. The
runtime writes nothing: compiled code places a continuation frame the same
way, through the same `emit_closure`.

A scalar box is placed the same way. `fz_box_int_for_any`,
`fz_box_float_for_any` and `fz_box_opaque_for_any` (a reference's word; a pid
is packed into its ref and has no box) are rows, and a call site asks
`emit_box(body, symbol, args)`. `native_codegen/scalar_box.rs` places one
16-byte slot, counted as a `ScalarBox`, stores the one payload word and answers
the box's address under the value's kind; the slot's second word is padding the
runtime leaves unwritten too. A float whose exponent bits are all ones (a NaN
or an infinity, which a foreign function can return) is not a language value:
the row sends it to `fz_box_float_for_any`, which raises, so the refusal is the
runtime's on every path. The receive dispatch bodies are entered from Rust with
the process as a parameter rather than in the pinned register, so they still
call the three functions (`runtime_call!`, not an inline row).

A binary field is a row too. `fz_bs_slice_ref(process, source, pos, bit_len)` takes a window the
caller has proved lies inside the source and answers what `Heap::slice` makes of it; a call site asks
`emit_slice(body, symbol, args)`. `native_codegen/binary_slice.rs` copies in place a window that starts
and ends on a byte boundary, is at most 64 bytes and is not the whole source, as an inline bitstring
counted as a `Bitstring` site (one object size when the length is a constant, five sizes for a length
known only at run time), and calls the function on a cold path for every other window. The bytes
address is read from both possible words and chosen by the source's kind, so the source's form costs no
branch. The receive dispatch bodies and the interpreter call `fz_bs_read_binary_ref`, which reads the
field's width from its spec and calls `fz_bs_slice_ref`.

The rows are the typed `fz_op_*_ii` arithmetic and comparison externs, the
bit operations `fz_op_band_ii`, `fz_op_bor_ii`, `fz_op_bxor_ii`, `fz_op_bnot_i`,
`fz_op_bsl_ii` and `fz_op_bsr_ii` (the two shifts are checked: a shift whose
result needs more than 64 bits fails; the recipe is a branch-free select between
the left and right shift), the
`fz_op_*_ff` comparisons, `fz_op_neg_f`, `fz_op_abs_f`, the list-cell,
list-reuse, struct, closure, scalar-box and binary-slice allocations above, and the helpers
`fz_type_of`, `fz_truthy_ref`, `fz_unbox_int`, `fz_unbox_atom`,
`fz_struct_schema_id_ref` and `fz_value_eq_raw_const` (an atom or integer
constant kind only; another kind keeps the call). The Rust function stays the
definition and the interpreter keeps calling it. To add an intrinsic, add one
`recipe!` row and one entry in `proofs()` in `recipe_test.rs`: the parity test
compiles every row and compares its answer with the runtime function over
inputs for its signature, and fails for a row with no entry. An allocation row
has an entry in `cell_proofs()`, `object_proofs()`, `box_proofs()` or the slice test (`SLICE_SYMBOL`) instead, and its test
compares heaps: it runs the runtime function (or heap method) in one fresh
process and the row's instructions in another, with room in the tip and with a
full tip. A cell is tried over every head kind, each with a tail of `[]` and of
a list, and the test compares the placed cell's words, the words of every
object the row may share, the tip each leaves, and the heap's allocation
statistics and object count. A struct is tried as tuples of several sizes,
named structs and a size that parks alone, and a closure with no, one and many
captures, each halt kind and the internal denotation; the test compares the
words the row writes (the header, and for a closure the code address) with the
same tip, statistics and object count.

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
Opaque    a pid or a reference: one word in an integer register, held as a
          value of its own kind (`ValueKind::PID` or `ValueKind::REF`)
Any       one opaque fz value word         Unit   maps to 0 on return
Binary    under "C": *const u8 to the bytes, no NUL guarantee (caller passes
          length). Under "fz": the tagged value ref.
CString   under "C": *const u8 to the bytes with a guaranteed trailing NUL.
          Under "fz": the tagged value ref.
Never     no return lane; returning is a runtime contract violation
StoredValue  a parameter only: two integer words, the word a container stores
          for a value of any kind (a scalar's bits, or an object's address
          with its literal bit) and the value's kind. Spelled `stored_value`.
```

A `stored_value` parameter is how a runtime helper takes a value of any kind
without a box: `:maps.put` guards `is_map` and calls `fz_map_put(map,
stored_value, stored_value)`, and `Map.delete` and `Map.has_key?` take their key the same
way, as do `fz_inspect`, `fz_inspect_with` (its value; the options stay a
reference), `fz_value_cmp_ref` and the equality externs `fz_op_eq`,
`fz_op_neq`, `fz_op_identical` and `fz_op_not_identical`. The runtime
entries `fz_value_eq_ref` and `fz_value_eq_widening_ref`, which compiled code
calls for `===` and `==` of two values it cannot type, take both operands as
the same words. The helper rebuilds each value with `Stored::value`
(`runtime/src/any_value.rs`). Natively the pair is
`native_codegen::stored_parts`: a value whose kind codegen knows gives its
word and a constant kind, and any other is read through its reference. The
interpreter passes the words of `Stored::of`. The lookups compiled code calls
without an extern, `fz_map_get_ref` for `Map.get` and
`fz_matcher_map_get_ref` for a map pattern, take their key as the same two
words, and `fz_struct_store_ref` and `fz_closure_set_capture_ref` take the
value they store as the same two words. A closure capture slot and a struct
field each hold a raw word and a kind byte, so a number in a register is
stored as it is. `CodegenFn::store_closure_capture_value` shares a heap value,
reads its parts with `stored_parts` and makes the call. Like an `any` slot, the slot takes a value
whole, so a tuple or a closure crosses it as one reference
(`ExternTy::takes_a_whole_value`).

One table in `src/extern_contract.rs` names every source spelling of a wire
type. Each row carries the `ExternTy` the spelling means, whether a declared
parameter takes its lane from the spelling (`binary`, `cstring`, `c_int`,
`unit`, `nil`) or from its semantic type through `ty_to_extern_ty` (everything
else, so an alias or a constraint can widen it; `atom` and `bitstring` read as
`Any`, so their word passes through unchanged), and, for a wire-only spelling
the type system has no type for, the semantic spelling the contract is
rewritten to before the type checker sees it: `cstring` to `binary`, `c_int` to
`integer`, `unit` to `nil`, `binary_cursor` to `bitstring`, `stored_value` to
`any`.

A wire-only spelling names one lane, and a lane is a whole register, so it
stands only as a whole parameter or result. Written inside a larger type,
`:: {c_int, integer}`, `extern_semantic_contract` refuses the contract with
`ExternContractError::WireSpellingInsideType` before any door resolves it, and
the diagnostic names the spelling and states the rule rather than reporting an
unknown type name. The sentence is built from the spelling table, so a new
wire-only row needs no new message.

The spellings, and what a declaration writes:

```text
integer  float  boolean  atom  any  binary  cstring  c_int  unit  nil  none
```

### A C `int` is narrower than an fz integer

`c_int` is fz `integer` semantically — a parameter accepts one and a result is
one — and 32 bits physically. The width is what the declaration is for:

```fz
extern "C" defp libc::open(c_string, c_int, ...) :: c_int
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

A field of a tuple has no register of its own, so writing `c_int` inside one is
the misplaced-spelling refusal above.

`fixtures/01424_c_int_negative_return` pins both signs on all three doors, and
`compiler2_native_lowering_narrows_c_int_arguments_and_sign_extends_c_int_results`
pins the reduce and the sign extension in the lowered CLIF, which is what the
declaration means on every host rather than on this one.

### One scalar result

An extern result is one scalar. A tuple result, `:: {integer, boolean}` for
instance, is refused where the contract is derived (`extern_return_wire`,
`src/compiler2/jobs/contract.rs`) with `lower/unsupported`, and the message names
`raises:` and `message:`, which declare a failure the operation can report.
Aggregate arguments are refused at the same boundary.

### A declared failure

An `extern "C"` whose C function can fail carries the failure beside its
result type, in a keyword tail on the declaration:

```fz
extern "C" defp fz_op_rem_ii(integer, integer) :: integer,
  raises: ArithmeticError,
  message: "bad argument in arithmetic expression"
```

The declared result is the plain `integer` or `float`. The C function returns
the `{value, failed}` scalar pair, `failed` being a canonical 0 or 1 word, and
the pair is physical only: no fz tuple is built, and no declaration spells it.

- `parse_extern_raises` (`src/compiler2/frontdoor.rs`) reads the tail. `message:`
  is required, because an exception carries no default message, and it is a
  literal string: an interpolated one is refused. The exception is a module
  alias. The tail takes one option, `raises:` or `delivers:` (below)
  (`parse_extern_option`). The parts ride the
  quoted extern map as `raises` and `message`, and `decode_extern_fn` carries
  them on `FunctionSurface::extern_raises` as `ExternRaises`, with the span of
  the alias.
- A declared failure is the struct literal `%Alias{message: "text"}`, and the
  alias must name an exception. `derive_function_contract` refers to the
  struct the way a body that wrote that literal does
  (`reference_declared_exception` calls `record_struct_reference`,
  `src/compiler2/jobs/body.rs`), at the alias's span, and waits for
  `StructDefined`. The reports a struct literal gets are therefore the ones
  `raises:` gets, at the alias: a name nothing defines is
  `resolve/unknown-module`, a module with no struct is `resolve/not-a-struct`,
  and an exception that declares no `message` field is
  `resolve/unknown-struct-field`. A struct that `defstruct` declared, not
  `defexception`, is `resolve/not-an-exception`.
- `extern_failure` resolves the alias with `World::module_alias_atom`,
  the call a body makes for `raise(KeyError, ...)`, so alias and import scope
  apply alike, checks that the struct's `__exception__` default is `true`, and
  builds `LastResort::declared`, which sets `message` to the declared text.
  The raised struct is completed as every last resort's is
  (`LastResort::struct_fields`, [exceptions](exceptions.md)): every field the
  exception declares, in its order, each other field holding its default (a
  `LiteralTerm`, `src/literal_term.rs`: a scalar, or a list, tuple or map of
  them), or `nil` when it has none. `checked_return` then makes
  the contract's return `ExternReturn::Checked(lane, LastResort)`. It refuses
  a non-`C` ABI and any result other than `integer` or `float`. Like the other
  ABI checks it runs for an extern that is called, and for an `extern "fz"` in
  user code the ABI reservation above is reported first.
- The native wrapper (`lower_extern_executable`) branches on the `failed` lane:
  the failing edge is `Term::Raise` with the declared atom and fields, the
  edge every decision's last resort already ends in, and the other edge returns
  the value. The atom is interned by `collect_executable_atoms`. A caller
  therefore tail-calls the wrapper; no continuation or decoder stands between it
  and the C symbol. A caller that is not in tail position and whose callee is
  frame-free, as an extern and any function that only calls externs are, makes
  the extern call itself (`lower_extern_here`, shared with the wrapper): the
  failing edge raises from the caller and the caller goes on in the same
  function (see [`pipeline`](pipeline.md), the delivered call lowered in its
  caller).
- The interpreter reads the same pair and answers `ExternCallValue::CheckedFailure`,
  which `continue_after_extern` hands to `raise_last_resort`, the function a
  decision's failure calls.
- A guard may call such an extern: the failure makes the clause not match, and
  nothing is raised (see [`pattern-matching`](pattern-matching.md#guards)).

Kernel's arithmetic externs (`+ - * / % div rem`, unary `-`, over integer and
float operands) are declared this way, so a failed operation, an overflow or a
zero divisor, raises `ArithmeticError` with Elixir's message. A user declaration
names any exception: `raises: MyApp.DivisionByZero` raises that module's
struct from a declaration of the same symbol, so with `defexception [:message,
code: 7]` a handler reads `e.code` as `7`.

### A call that delivers its argument

An extern whose call hands its first argument to the nearest handler says so,
and names the kind the handler receives:

```fz
extern "fz" defp fz_throw(any) :: none, delivers: :throw
```

`parse_extern_delivers` accepts `:error`, `:throw` or `:exit`. The kind rides
the quoted extern map as `delivers`, and `decode_extern_fn` carries it on
`FunctionSurface::extern_delivers` as a `RaiseKind`. The three raise
primitives in `lib/kernel.fz` (`fz_panic`, `fz_throw`, `fz_exit`) are declared
this way. The declaration changes no code: it tells the semantic analysis that
what the extern is called with is what a handler of that kind can receive (see
[exceptions](exceptions.md#what-a-handler-can-receive)).

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
  scalar return, the value and flag of a checked return — reads the bank from it.
- `lower_extern_generic` gives `F64` its own `LowerOut::RawF64` lane, and the
  return match is exhaustive on purpose. A wildcard there is what let `F64`
  default into the `ValueRef` arm in the first place.
- The interpreter cannot transmute an address by arity alone. `ArgWord` tags
  each argument with its bank. SysV x86-64 and AAPCS64 give a scalar argument
  the next free register of its own bank whatever the other bank holds, so
  `dispatch_shapes!` makes one call per return lane: the integer words in the
  integer registers in order, the float words in the float registers in order,
  and each bank padded to `MAX_INTERP_EXTERN_ARGS`. A callee reads only the
  registers its parameters name. Any other target is a compile error.
- `MAX_INTERP_EXTERN_ARGS` (6, the integer registers SysV x86-64 passes) is a
  ceiling the backend does not have, so a 7-word extern is refused under
  `interp` and runs under `run`/`build`. An `extern "fz"` spends one word on
  the implicit process word, and a `stored_value` spends two.
- A helper's Rust signature must be its declared wire types. The `fz_op_*`
  arithmetic shims took `u64` and bit-punned floats, which was correct only
  while the dispatcher bit-punned them too; fixing one half broke six fixtures
  until the other half was fixed.

`fixtures/01466_extern_float_lanes` pins the bank assignments on all three doors,
including both mixed orders — one alone cannot distinguish a correct table from
one with the two mixed shapes transposed.

## A variadic contract has a tail domain

A variadic extern's `FunctionContract` carries a tail domain alongside its
fixed parameters: the type every argument past the declared prefix must
belong to, `integer | c_pointer | binary`.
`extern_contract::variadic_tail_domain` builds it next to `ty_to_extern_ty`'s
own raw-word union, so the domain and the wire alphabet can't drift apart.
`FunctionContract::apply` widens a clause's parameter list by repeating the
tail domain until it matches an observed row's length, then matches through
the ordinary calculator (`Types::match_arrow`) exactly as it does for any
other arrow; a row shorter than the fixed prefix is still refused.

The domain decides whether a row FITS the declaration at all. Binary is in
it because an ascribed binary reaches the wire; float is not, because the
generated variadic call has nowhere to carry one. Once a row fits, the
marshal classes below decide the narrower question of which physical lane
each tail value crosses on — an un-ascribed binary is still refused there,
because the lane depends on an ascription the contract's row can't see.

A row that does not fit is a fatal `spec/violation` at the call, on every
door: an extern's declaration is enforced unconditionally, because it is the
whole definition and the row came straight from the one caller that made it.
`libc::printf("%f", 1.5)` names the tail domain past the fixed `fmt`
parameter in its diagnostic, marked `...` (`00253_variadic_float_error.fz`).

## An extern is a function with one typed clause

An extern's entry dispatch is a single row of wildcard patterns plus one type
precondition per declared fixed parameter, built by `extern_entry_preconditions`
(`src/compiler2/jobs/dispatch.rs`) from the contract's first arrow. The type
asked is `ContractArrow::entry_domain`: a variable with a bound reads as that
bound, an unbounded variable and `any` read as `any`, and a parameter that
admits every value adds no precondition. The row's precondition goes through
`runtime_type_test_envelope`, the same wrapping an annotated parameter of an
ordinary function gets, and its arm of last resort is the function-clause
error: `** (FunctionClauseError) no function clause matching in
fz_op_add_ii/2`. `rescue` catches it.

A call whose arguments are proven to fit the parameters leaves a plan that
wins its one outcome without asking, so `executable_dispatch` retains no
dispatch and the executable is the extern call alone on every door. A call with
an `any` argument keeps the test:

- the interpreter runs `select_clause` before `call_lowered_extern`
  (`step_extern_executable`, `ir_interp/backend.rs`) and raises the last resort
  when nothing matches;
- native lowering emits the dispatch in the executable and tail-calls a
  `<name>__call` function that holds the extern call
  (`lower_extern_executable`, `jobs/native.rs`), and `collect_executable_atoms`
  interns the last resort's atoms for an extern as for any clause body.

Which arguments the compiler refuses outright and which it tests at run time is
unchanged: an argument whose type is narrower than `any` and outside the
parameter's type is `spec/violation`; an `any` argument is tested.

So a runtime function that reads a binary declares its parameter `binary` or
`bitstring`, and its body is handed a proven binary. Where Elixir raises
something else for a non-binary, or names the public function in its
`FunctionClauseError`, the library function carries the guard Elixir's own
function head does: `String.length/1` and the grapheme functions test
`is_binary`, and `String.to_atom/1` and `String.to_float/1` raise
`ArgumentError` naming the first argument, as the BEAM does
(`01824_a_binary_function_given_a_non_binary_raises_what_elixir_raises.fz`).

### The runtime trusts the declared types

An extern declares the types it really takes and returns, and the runtime
helper trusts them: it does not test them again. The type check lives once, in
fz, where the compiler can see it and drop it when the argument is proven.
The map externs show the shape. `fz_map_put`, `fz_map_delete`,
`fz_map_has_key`, `fz_map_count`, `fz_map_keys`, `fz_map_values` and
`fz_map_to_list` take `map`, and `fz_map_put`, `fz_map_delete` and
`fz_map_from_kv` return `map`. `Heap::expect_map_layout` reads the layout of
its argument (flat, trie or struct, a choice of layout and not a type check)
and asserts only in a debug build that the value is a map; `read_map_value`
and `map_put_slot` do the same, and `fz_map_get_ref` has no error arm.

The library wrapper carries the proof forward:

- A function that raises `BadMapError` for a non-map keeps `any` for that
  parameter and guards it with `is_map`, or ends in a clause that raises
  `%BadMapError{term: x}` (`Map.put/3`, `Map.delete/2`, `Map.get/2`,
  `Map.has_key?/2`, `Kernel.map_size/1`, `:maps.to_list/1`, `keys/1`,
  `values/1`, `put/3`, `merge/2`). The compiler drops the guard for a caller whose argument is
  proven a map.
- A function that returns a map says `:: map` in its spec, so a loop that feeds
  one call's result to the next keeps the proof; a `:: any` return throws it
  away and every later call re-tests the kind.
- An `any` argument that reaches a `map` parameter unguarded is tested at the
  call and raises `FunctionClauseError`; the wrapper's guard is what makes the
  failure `BadMapError` as Elixir's.

`map_size(1)`, `Map.put(1, ...)`, `Map.delete(1, ...)`, `Map.get(1, ...)` and
`:erlang.is_map_key(:a, 1)` raise `BadMapError` carrying the term
(`01928_a_map_function_given_a_non_map_raises_badmap_and_a_put_loop_keeps_the_map_proof.fz`,
`compiler2_native_put_loop_over_a_proven_map_asks_no_kind_question`).

The entry test for `pid` and `ref` reads the value's kind: a pid passes
`pid` and a reference passes `ref`, and no integer, float, atom, binary or list
passes either. The test for `c_pointer` admits every value, because the
run-time type predicate has no axis for that type; an ordinary function
annotated `c_pointer` admits every value the same way. An ordinary function
annotated `pid` or `ref` is as exact as the extern's entry test.

The interpreter's `marshal_arg` keeps its conversions as internal-error guards:
after the entry dispatch an integer, float or boolean parameter always holds
the right kind of value, and a variadic tail argument is resolved by the
call-site marshal class instead.

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
@spec send(pid, t) :: t when t: any
def send(pid, msg), do: fz_send(pid, msg)
```

The body calls `extern "fz" defp fz_send(pid, t) :: t when t: any`, so the
message is boxed (the ABI adds the process alongside it, which the wrapper
never sees) and the result is a boxed `AnyValueRef`; reached for an `integer`,
the wrapper's return unboxes that word back to an `i64`. A repeated type
variable means "same type", not "same object" — boundary correctness is the
marshal class on the way in plus this coercion on the way out. The declared
bound answers only where the call pinned nothing, so `t` is whatever the
caller passed, the empty list included: `send(pid, [])` is typed `[]` and not `any`
(`types::arrow_match`, fz-kdt.120).

`fz_send`'s own return evidence is its `FunctionContract` applied to the
activation's row: the extern has no body to observe, so its declared clause
is the only witness it has for what it returns (see
[`semantic-authorities`](semantic-authorities.md), "what does an activation
return"). `send(pid, 1)` therefore defines its return as `int` once, and every
caller sees that value rather than the unconstrained `t`.

## One-word boundaries

A composite value crossing a place where the far side reads exactly one machine
word travels as a single boxed `ValueRef` lane, not as its unboxed leaves. One
predicate, `position_requires_value_ref` in `jobs/transport.rs`, names every
such place, and `with_value_ref_carrier` gives the layout that lane while the
layout keeps its structural shape. Two places qualify:

- an `any`-typed extern parameter or return holding a tuple or callable;
- the return of the root's entry executable (`World::root_entry_executable`)
  when it asks for its value and returns a tuple. The driver ends a program by
  tail-calling a halt continuation declared `(value, self)`, so the root hands
  it one word; the host reads that word as the program's result.

Scalars are already one word and stay raw at both. A root that asks for a tuple's
fields (`ExecutableNeed::TupleFields`) is read structurally and is not a
boundary. A root whose body tail-calls a function returning a wide tuple becomes
a delivered call: the callee's lanes arrive in a continuation that boxes them.
`native_return_halt_repr` (native_codegen/delivery.rs) enforces the invariant
when the entry is bound: a root body returning anything but one lane is a
`CodegenError`. A spawned zero-argument callable is bound through its wrapper,
which returns one `ValueRef`, so its halt kind is `ValueRef` whatever lanes its
member returns.

## Helpers that read the driver's context

A helper may read what its driver put on the process's `ExecCtx` instead of
taking it as an argument. `System.argv/0` wraps a private
`extern "fz" defp fz_system_argv() :: any` under `@spec argv() :: [binary]`:
the extern returns a boxed `any`, and the wrapper's spec narrows it to a list of
binaries. `fz_system_argv(process)` takes only the process the `fz` ABI
adds, reads `process_ctx(process).argv()`, and allocates one binary per argument
from its raw bytes. The JIT, the interpreter and the AOT scheduler each fill
`ExecCtx.argv`; see [`runtime-telemetry`](runtime-telemetry.md), "Program
Arguments".

## The one output extern (and the warning extern)

`IO` prints through a single private
`extern "fz" defp fz_io_write(binary) :: unit`. `fz_io_write(process, binary_ref)`
hands the bytes of a byte-aligned binary, exactly as given, to `write_output`
in `runtime/src/lib.rs`, which passes them to the running process's output
hook. It returns `unit`, so a print allocates nothing; `IO.write/1` and
`IO.puts/1` answer `:ok` themselves. No output extern appends anything: the
caller owns the newline, so `IO.puts/1` concatenates `"\n"` itself and
`IO.write/1` does not. `Kernel.dbg/1` is `IO.inspect/1`, so every print on the
interpreter, JIT and AOT paths ends in this one function.

`IO.warn/1,2` reports through one private
`extern "fz" defp fz_io_warn(binary, binary, integer) :: unit`: the message, the
file it points at (the empty binary is no location) and the line. The Elixir
forms (`Macro.Env`, a keyword with `:file` and `:line`, `[]`, a stacktrace) are
reduced to those three in `lib/io.fz`. `fz_io_warn` hands them to
`write_warning` in `runtime/src/lib.rs`, which calls the process's
`ExecCtx.warn` hook with the context `output` uses.

## A helper that may have no answer

A helper cannot build a tuple or pick between a tuple and an atom, so one that
may have no answer returns a list the wrapper takes apart. `Float.parse/1`
wraps a private `extern "fz" defp fz_float_parse(binary) :: any`, which returns
`[]` when the binary does not start with a float and `[float, rest]` when it
does; the wrapper's clauses turn those into `:error` and `{float, rest}`. The
prefix rules and the rounding live in the one Rust function behind it
(`float_prefix` in `runtime/src/ir_runtime.rs`), so all three paths share
them.

`Macro.escape/1` asks what a function is called through the same shape: a
private `extern "fz" defp fz_function_name(fun) :: any` answers
`[module, name, arity]` for a function a module defines by name and `[]` for
an anonymous function or one outside every module.

`File.Stream` reads each line through the same shape: a private
`extern "fz" defp fz_file_read_line(c_pointer) :: any` answers `[]` at end of
file and `[line]` otherwise, and the stream's `line_step/4` clauses match the
two. The `c_pointer` is the `FILE *` the stream reads from its `File.open/2`
handle's `.value`. The Rust helper gathers the bytes up to and including `\n`
(or the trailing bytes of a file that does not end in one) with C `getline`, one call per line
into one buffer and allocates the binary once; a line that ends in `\r\n`
comes back ending in `\n`, which is what Elixir's `File.stream!/1` yields, and
any other `\r` stays. `read_line_bytes` in `runtime/src/ir_runtime.rs` holds the
splitting and `ir_runtime_test.rs` pins it.

`File.read/1` takes the whole file through one more such helper: a private
`extern "fz" defp fz_file_read_rest(c_pointer) :: binary` answers every byte
from the `FILE *`'s position to the end. `read_rest_bytes` in
`runtime/src/ir_runtime.rs` reads 64 KiB blocks with C `fread` into one growing
buffer, so the stream need not be seekable or have a known size, and the binary
is allocated once (off the process heap, in a shared buffer, above the inline
threshold). A read error ends the bytes early; `File.read/1` then asks `ferror`
and answers `{:error, :io}`. Fixture 01761 pins the allocation, and
`ir_runtime_test.rs` pins the block boundaries.

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
extern "fz" defp fz_make_resource(t, (t -> nil)) :: resource(t) when t: integer | cpointer
@spec make_resource(t, (t -> nil)) :: resource(t) when t: integer | cpointer
```

The destructor captures nothing. It is a literal closure (`is_literal()` on its
ref), which the `Resource` keeps as a word outside every heap. `fz_make_resource`
is the one place that decides this: it answers `nil` (an atom, never a resource
ref) for a closure that captures, and `Kernel.make_resource` turns that `nil`
into `ArgumentError` "a resource destructor captures nothing", which the program
can rescue. No type or spec checks it. A destructor that is not a closure at all
is a spec violation and an internal assertion in `fz_make_resource`.

`resource(T)` is a real type constructor on the `Types` trait; the variable binds
from the payload, so `make_resource(42, &close/1)` is `resource(integer)` --
`fz_make_resource`'s return evidence, like every extern's, is its own
`FunctionContract` applied to the call's row, not a type the extern's
(nonexistent) body could observe. A
module that declares `@type t :: opaque resource(integer)` brands that shape as
`t` wherever a position is annotated `t` — `mint_brand(resource(integer), tag)`,
the identical mechanism `refines` uses (see
[`set-theoretic-types`](set-theoretic-types.md)). The brand is nominal — two
brands over one inner meet at empty — so a plain `resource(integer)` and the
module's `t` are two different `@spec` positions, even though every `t` value is
structurally a `resource(integer)`.

`.value` on a resource handle projects the payload from any module that holds
one; lowering keeps this as ordinary field access, and both backend interpreter
and native/JIT/AOT paths read it through the shared named-field runtime ABI. An
opaque type's structure is not hidden from code outside its declaring
module — routing every read through an accessor the declaring module defines
is a convention, not an enforced boundary.

`Kernel.claim_resource/1` is the deterministic counterpart to fallback
cleanup. It reads the payload and then atomically claims the shared off-heap
resource, returning `{:ok, payload}` to the one winner or `{:error, :closed}`
to every other alias. A claim is visible through aliases in other processes and
disarms the FZ destructor at final release. The successful caller must perform
cleanup itself. The claim and payload read are one non-yielding runtime-library
operation today; resource users must not expose a raw payload to application
code before they own it.

## Externs called from guards

Every extern is callable from a guard; the guard-expression node is
`PatternGuardExpr::Extern`. `GuardExtern::new` (dispatch_matrix/pattern.rs)
admits parameters of class `I64`, `Opaque`, `F64`, `Any`, `StoredValue` or `BinaryCursor` and returns of `I64`,
`Opaque`, `F64`, `Any`, `Bool` or `Never`, plain or `Checked`; any other class
is `SourcePatternError::GuardExternClass`, a compile error on every path. The
receive matcher's shim (`emit_guard_extern`) therefore marshals five classes
of operand: an integer (`receive_value_int`), a float (`receive_value_float`),
a pid or reference (a pid is read from and packed into its ref inline; a reference goes through `fz_unbox_opaque` on the way in and `fz_box_opaque_for_any`
on the way out), a reference word (`emit_receive_value_ref`) and a stored word
with its kind (`receive_value_stored_parts`, two arguments, no box); a `Bool` return is a nonzero
word read as the atom `true` or `false`. `===` and `!==` in a guard are the
Kernel functions a body calls, so they reach `fz_op_identical*` and
`fz_op_not_identical*` through this node. An extern returning `none` fails the
guard without being called, and a `Checked` extern that reports failure fails it
too. The interpreter calls the extern through `call_lowered_extern`;
native lowering emits `Prim::Extern`. Domain checks live in the Kernel heads
that wrap the primitive (see [`pattern-matching`](pattern-matching.md)).

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
cargo test --test fixture_matrix 00605_libc_abs_arg_outside_declared_domain  # row outside a fixed extern's domain, 3 doors
cargo test --test fixture_matrix 00253_variadic_float_error  # row outside a variadic extern's tail domain, 3 doors
cargo test --test fixture_matrix 01110_an_any_passed_to_a_typed_extern  # entry test of a typed extern, 3 doors
cargo test --test fixture_matrix 01111_a_function_clause_error_from_a_typed_extern  # rescued, 3 doors
cargo test --lib extern_entry_dispatch  # preconditions per parameter type; proven call asks nothing
cargo test --lib compiler2::contract_test::extern_row_outside_its_declared_contract_is_a_spec_violation
cargo test --lib compiler2::contract_test::variadic_extern_violation_names_the_tail_domain_past_the_fixed_params
```
