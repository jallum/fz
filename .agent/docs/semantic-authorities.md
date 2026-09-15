# Semantic authorities

A semantic question is one whose answer is part of the language: is this value
true, are these two values equal, which of them is smaller, is this a binary.
Every such question is answered on three doors — interpreter, JIT, AOT — and the
doors must agree.

This note says, for each question, WHO OWNS THE ANSWER and which per-door fast
paths are allowed to sit beside it. A fast path is legitimate: quicksort's
zero-scalar-box allocation pin depends on an inline both-integer compare, and
boxing two integers to ask a shared function would defeat it. What is not
legitimate is a SECOND ANSWER — a door deciding the question itself, so that
changing the rule in the owner leaves the other statement behind.

The list exists because counting is the diagnosis. Every divergence this epic
found was the same shape, and in each the count was knowable before the bug was:

| question | answers found | how it showed |
| --- | --- | --- |
| ordering | 3 | `2 >= 1.0` false on JIT, true on interp (fz-5xp.18) |
| is this a binary | 4, two wrong | a binary over 64 bytes matched no pattern, silently (fz-5xp.57) |
| inline or shared storage | 6 | one caller already disagreed with the heap (fz-5xp.45) |
| where a foreign symbol lives | 4, three dlsym | passed on macOS, failed on Linux, one door at a time (fz-5xp.59) |
| what is this bitstring field | 2 lowerings | two tail allocations per scan step (fz-5xp.56) |

## The table

**Closure denotation** — owner `World::FunctionMap`. Named functions have a
typed module/name/arity origin; generated lambdas have their shared owner's
origin and a `LambdaOccurrence` assigned in final quoted-function decoding's
existing recursive traversal. Immutable AST clones preserve that occurrence,
including the `with` lowering that emits its `else` at each failed binding.
Source spans are diagnostic metadata, so repeated metadata-identical
macro expansions cannot alias definitions. `FunctionId::denotation` projects the
same World identity into interpreter, JIT, and AOT closure headers. Specializing
code or changing capture layout does not change it. The ID answers equality of
source denotations, not order: `FunctionRef::semantic_cmp` compares typed origins
and numeric arity. `Types` shares these immutable origins with `FunctionMap`;
neither canonical labels nor generated display names are comparator inputs.
The same immutable `FunctionDenotation` is shared with the runtime Node. Closure
construction registers the source origin; JIT/AOT publish typed origin data
with their program. Runtime comparison asks the Node for source order, never
orders numeric denotation IDs. A closure's one retained environment stores one
complete value per lexical capture; execution wrappers project that environment
into their own ABI layouts without changing its identity.
`CallableDescr` interns only function, arity, and ordered physical capture
layouts. Each construction owns its ordered source capture annotations, carried
unchanged into the backend wrapper and its runtime type predicate. Distinct
annotations can therefore share one physical descriptor without sharing a
construction's semantic type; invocation target prefixes supply neither.

**Truthiness** — owner `fz_truthy_ref` (`runtime/src/ir_runtime.rs`). The rule is
"every value is true except `false` and `nil`". `fn_ctx::truthy_ref` and
`receive::emit_truthy_cmp` call it; the interpreter's `AnyValue::is_truthy`
(`ir_interp/value.rs`) is the interp-side statement of the same rule, and is
now the only one there — `ir_interp/mod.rs` carried a second copy until
fz-5xp.21. `emit_truthy_cmp` keeps typed fast paths that restate the rule inline
for a known-Atom operand and answer a constant `1` for a known Int or Float;
those are sound because a number is never false, but the Atom arm is a
restatement and would have to move with the rule.

**Equality — two questions, and the IR names both.** `TermComparator::compare`
(`runtime/src/term.rs`) owns comparison over borrowed immutable values, Node,
and SchemaRegistry. `NumericMode` selects the semantic question:

  * `Widening` is the `==` OPERATOR. Numbers compare by value, recursively,
    so `1 == 1.0`, `[1] == [1.0]` and `%{a: 1} == %{a: 1.0}` are all true —
    while `%{1 => :a} == %{1.0 => :a}` is false, because widening applies to
    values and never to the keys that decide which entries line up. Entry
    points `fz_value_eq_widening_ref`, `interp_operator_eq`, and IR
    `BinOp::Eq`/`Neq`.
  * `Strict` is STRUCTURAL IDENTITY: `===`, a pinned match, a map key,
    `Enum.member?/2`, `--`, and every kind of pattern matching. `1` and `1.0`
    are different values, as are the two signed floating zeros. Entry points `fz_value_eq_ref`, `interp_value_eq`,
    and IR `BinOp::Identical`.

The IR ops are the load-bearing part. One `BinOp::Eq` used to serve both, with
the question decided by a `widen_numerics` boolean that each lowering CALL SITE
set from what it knew about its caller — so a guard, which reached the matching
call site, answered `same?(1, 1.0)` as `:different` where Elixir says `:equal`
(fz-5xp.24). Both doors agreed, which is why it read as correct: it was one
operator with two meanings, not a divergence. The lowering now derives the
question from the op, so a call site cannot get it wrong.

**Ordering** — the same `TermComparator`, reached through `fz_value_cmp_ref`
and unboxed scalar adapters, owns every published finite term's order:
`number < atom < reference < fun < port < pid < tuple < map < list < bitstring`.
For the atom category it delegates to `Node::cmp_atom_names`, the single owner
of atom name order. Atom ids are handed out in first-seen order, so ordering by
id would depend on which atom the program mentioned first. Ordinary comparison
reaches the node through its process; each process heap shares that same node so
map ordering asks the same question without ambient process state (fz-5xp.90).

`interp_cmp` shares unboxed numeric handling across expressions, intrinsics,
and guards. Same-kind native lanes use integer/float instructions; mixed lanes
call `term::compare_int_float` through `fz_int_float_cmp`, the same exact helper
used by `TermComparator`. No integer is rounded through `f64` before comparing
its magnitude. Strict mode breaks equal numeric magnitudes by kind and retains
signed-zero identity; widening mode equates signed zeros.
`fz_value_cmp_raw_const` compares a ref against an unboxed payload without
allocating a scalar box.

For the ORDERING operators `Kernel` declares a typed clause per numeric pair
and a final `any`/`any` clause through `Kernel.compare/2`, so `1 < :atom`
answers `true` by the total term order rather than being refused. That is the
same shape `==` and `===` have; ordering, equality and identity are all total
functions, so each catch-all answers a real pair rather than standing in for a
missing one. `Enum.sort/1` calls `compare/2` directly. The ordering operators'
`binary` clauses are commented out in `Kernel` rather than deleted: a `binary`
clause compiles to a runtime test that proves only "bitstring", so seating one
ahead of the catch-all would send an unresolved operand to the byte compare
without proving the surface the clause names, and the blind-escape census
cannot justify the seat. Binaries are ordered by the comparator's bitstring
branch through the catch-all instead, and the clauses come back as the fast
path when `RuntimeTestAxis::precision` stops calling `Binaries` erasing.

**Arithmetic and comparison exports** — `runtime/src/ir_runtime.rs` owns the
real C functions, and the `Kernel` extern declarations own how they are called.
Neither interpreter nor native code discovers behavior from a symbol spelling
or suffix. The interpreter calls the real export through the
ordinary FFI path, and both arithmetic and comparison exports remain ordinary
calls in native code too.

Fallible arithmetic returns an unboxed `{result, boolean}` C scalar pair.
The runtime returns initialized values and a canonical status word; Kernel's
sole `arithmetic_error/0` helper turns `true` into the temporary `panic(:badarith)`
policy. Numeric comparisons — ordering, equality and identity alike — are raw
`extern "C"` calls on unboxed integer and float lanes. Binary and
general-value comparisons use the ref-carrying `fz` ABI instead, so they
retain process/schema context rather than pretending a C byte pointer has a
length; that ABI is what `==` and `===` reach through their `any`/`any`
clause.

`%` is the one operator with no Elixir counterpart to be checked against —
Elixir has no `%`, and its `rem/2` is integer-only. fz's `%` is C's `fmod`, so
the result takes the sign of the dividend, and its float lanes are a CALL rather
than an instruction because Cranelift has no `frem`: the real
`fz_op_rem_{if,fi,ff}` exports retain that one fmod-backed call on native paths.

**Runtime type tests** — owner `RuntimeTestAxis` (`src/runtime_type_predicate.rs`),
one axis table with three lowerings that must each be taught, and the design we
want everywhere. The claim held under audit, with one hole: an axis is a
question about a language VALUE, not a storage kind, and a binary has two
representations. `ValueKind::BINARY_REPRS` names them once so every lowering
reads the same fact (fz-5xp.57).

**Source struct matching** — the source producer in `dispatch_matrix::pattern`
asks the same `Region::Type` question with a World-resolved tagged-record `Ty`.
Its success evidence owns named `StructField` projections. Field names are
source atom keys; schema module identity is typed, and neither tuple storage
offsets nor a rendered type name participates in clause selection. Interpreter,
local native dispatch, and receive dispatch consume this shared plan and use
the existing named-field accessors.

**Bitstring field source semantics** — owned by the final quoted-source decoder in
`compiler2/quoted_function.rs`. A raw field has the language's integer default,
but quoted source represents an unsuffixed string field as the raw binary value:
there is no `:: binary` node downstream can consult. The decoder therefore
reifies that one source shape as `BitType::Binary`. Construction leaves its
size absent so the writer consumes the whole source binary; matching adds the
literal's byte length so a following field has a boundary. Backend lowering and
the three runtime doors consume that spec and never reinterpret a value's
carrier from the surrounding fields.

Bitstring matching has one runtime implementation, `fz_bs_read_field_bits`,
reached from every door. But the CLAUSE HEAD is lowered twice — once into a
dispatch region to select the clause, once into body steps to bind — so each
field is read twice: fz-5xp.56.

**What a dispatch plan demands** — owner `DispatchGraphBuilder`
(`dispatch_matrix/mod.rs`). The builder folds each question into
`DispatchGraph::input_demand` as the node is added, one slot per DECLARED input,
and every reader reads that recorded fact: the interpreter through
`PatternDispatchPlan::input_demand`/`required_input`, native lowering through
`required_input`, the executable facts through
`ExecutableFacts::entry_dispatch_demand`, and activation keying by taking the
slice as a body's local demand. A slot that stays `Ignore` is an input the plan
never reads, and a backend is free to pass it as nil.

Three rules decide what a question charges. A test charges its own subject at
the demand its region asks for, plus the input that delivers any pin it names --
a pinned equality, or a bitstring field whose size was bound before the pattern
began. A guard rides a CARRIER subject that it need not read -- input 0 when
the plan declares one, and a subject minted for the purpose when it declares
none -- so the carrier is not charged and the guard's leaves, the subjects and
pins its expression reads, are charged instead. Edge evidence is
not charged at all: a proof restates its test's predicate, and a projection is a
binding under a test that already charged its root, which `build` asserts before
it hands the graph over.

A guard helper is reified as a NESTED plan numbered in its own input space and
fed only through the call's argument list. Its leaves are the caller's, derived
from the finished expression when the plan is finished, so the helper's own
numbers never reach the caller's slots. A collector that walked the nested plan
instead made a 3-input helper called from a 1-input clause demand semantic input
2; native dispatch iterates its own inputs and asks whether each is required, so
it never looked at the impossible ordinal, while the interpreter iterated the
demands and indexed the arguments, so it refused the call (fz-5xp.74). Charging
asserts every ordinal is inside the declared count, which keeps a recurrence at
the plan that produced it rather than at whichever door reads it first.

**Map key identity and order** — `TermComparator` in `Strict` mode owns both.
Tuple/list/map keys compare structurally; binary storage kinds share bit
identity; `SchemaIdentity` distinguishes tuple arity from named source module
segments. Neither flattening a module name nor parsing a rendered schema label
participates in schema publication, transport, or comparison.
The registry rejects a second layout for an existing identity, so one borrowed
schema can read both compared objects without a layout compatibility path.
Closures compare source denotation then exact environment; resources compare
the generative `ResourceId` on their existing off-heap owner. Schema indices,
display labels, wrapper IDs, and physical capture lanes never decide map key
identity or order. After validity checks, exact retained value identity proves
equality without descending; distinct addresses prove neither inequality nor
semantic order.

Both public heap builders feed one normalization function: a stable sort and
last-value-wins dedup at publication. Destination freeze compacts that same
allocation. Put, delete, and lookup share one binary search; updates copy the
ordered sequence directly, absent deletion returns the original allocation,
and GC/transport preserve order without sorting. Iteration consumes this stored
order directly. Quoted-source equality erases diagnostic metadata, which can
change key order; its distinct relation matches entries without assuming that
metadata-erased keys retain runtime order.

Published terms are finite immutable DAGs. Proper list construction rejects
non-list tails; low-level struct/closure/map writes require exclusive unpublished
ownership. Map destinations carry construction state and cannot re-enter it
after freeze. Checked float construction, ref decoding, and scalar-box ingress
reject nonfinite payloads. Collector-only cyclic test graphs stay outside term
comparison. Comparison defensively rejects unfinished maps, internal absence,
forged nonfinite floats, and unregistered atom IDs; none receives a fallback
language order.

**Binary representation** — owner `ValueKind::BINARY_REPRS`
(`runtime/src/any_value.rs`). Inline `Bitstring` below
`SHARED_BIN_THRESHOLD_BYTES`, shared-buffer `ProcBin` above it.

**Inline or shared storage** — owner `Heap::alloc_bitstring`, which returns the
VALUE rather than a pointer the caller re-classifies (fz-5xp.45). Two other
readings of the threshold remain and are different questions:
`alloc_bitstring_suffix` asks whether a VIEW is worth a stub, and native codegen
asks what to EMIT for a constant bitstring, which it must answer at compile time
with no heap to ask.

**Where a symbol lives** — owner `fz_extern_symbol_addr`
(`runtime/src/symbol_lookup.rs`), for fz's own exports and foreign ones
alike. The interpreter's `resolve_symbol` and its variadic path call it, and
the JIT is built with it as its `symbol_lookup_fn` rather than cranelift's own
dlsym. Neither door keeps an address table: the compiler's binaries and test
binaries export dynamically (`build.rs`), so fz's own exports are in the
process to be found. The AOT door is answered by the linker instead, which is a
fourth place and why `-lm` is hardcoded until a declaration can say which
library it comes from.

**How a C variadic call is made** — owner `emit_variadic_c_call`
(`native_codegen/variadic.rs`). Cranelift cannot mark a call variadic, so the
platform's variadic placement is produced by choosing the call's parameter
list, and one function makes that choice for every target. Native codegen calls
it directly; the interpreter reaches it through a generated trampoline, so
there is no second description of the ABI to drift. Its correctness rests on
variadic arguments being integers and pointers only, which the marshal front
end enforces.

**How a runtime helper is typed at a compiled call site** — owner the Rust
function item. `runtime_call!(body, fz_list_cons_int, [process, head, tail])`
reads the linker symbol off the identifier and the Cranelift signature off the
item's type (`native_codegen/runtime_call.rs`), so a compiled call cannot
describe a helper differently from the function it reaches. The helper is
declared on first use in each body; there is no table of helpers to keep in
step with the runtime.

**UTF-8 validity and prefix errors** — owner `utf8_prefix`
(`runtime/src/ir_runtime.rs`). It recognizes one codepoint as either a valid
width or the first byte offset at which that prefix becomes impossible. The
whole-binary `fz_bitstring_valid_utf8` folds that decision over the input;
`fz_bitstring_utf8_prefix` exposes one decision to `Utf8.next/1`, which returns
a branded codepoint or the original suffix beginning at the offending byte.
Parsers consume that suffix to recover a source offset. They do not carry a
second UTF-8 table or validate a whole document before its syntax is parsed.

**UTF-8 scalar encoding** — owner `encode_utf8` (`runtime/src/bitstr.rs`),
reached by an fz `<<codepoint :: utf8>>` segment. `Utf8.from_codepoint/1` is
the checked public constructor: it excludes negatives, the UTF-16 surrogate
hole, and values above U+10FFFF before invoking that segment, then brands the
result. A format parser such as `Json` owns its format-specific scalar syntax
(including joining a UTF-16 surrogate pair) and hands the resulting integer to
this constructor; it does not carry another UTF-8 encoder.

**Text** — `String` (`lib/string.fz`) is plain fz over
binaries, and declares three primitives of its own: `to_atom/1`, which reaches
the node's atom table, and `fz_binary_upcase`/`fz_binary_downcase`. It does not
declare `byte_size/1`; that comes from `Kernel`. Everything else is recursion
over a binary, which is only affordable because a tail is a view and a computed
size can be matched.

Case mapping is the one place the owner is a Rust table rather than fz. It is
FULL Unicode casing — `char::to_uppercase` and its inverse, all 103 special
casings, so `"straße"` upcases to `"STRASSE"` — and the oracle twins check it
against Elixir's DEFAULT mode, not `:ascii`. The table lives in the runtime
because as fz clauses its 2,723 pairs would go through the dispatch matrix and
make compile work proportional to the table rather than to the program; it
belongs in fz once a table can be data rather than clauses (fz-5xp.68).

## Reading this list

Two properties make an entry safe. The rule is stated once, and the places that
do not state it can only ASK. Where a door restates the rule — the Atom arm of
`emit_truthy_cmp`, `guard_cmp`'s numeric arms — the restatement is narrower than
the rule and cannot answer a case the owner would answer differently.

Where an entry names a ticket, that question currently has more than one answer
or an answer that is not yet complete. Adding a semantic predicate to fz means
adding a row here, not just an implementation.
