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

**Truthiness** — owner `fz_truthy_ref` (`runtime/src/ir_runtime.rs`). The rule is
"every value is true except `false` and `nil`". `fn_ctx::truthy_ref` and
`receive::emit_truthy_cmp` call it; the interpreter's `AnyValue::is_truthy`
(`ir_interp/value.rs`) is the interp-side statement of the same rule, and is
now the only one there — `ir_interp/mod.rs` carried a second copy until
fz-5xp.21. `emit_truthy_cmp` keeps typed fast paths that restate the rule inline
for a known-Atom operand and answer a constant `1` for a known Int or Float;
those are sound because a number is never false, but the Atom arm is a
restatement and would have to move with the rule.

**Equality** — owner `fz_value_eq_ref` (`runtime/src/ir_runtime.rs`). Both
`lower_eq_binop` (native) and `interp_value_eq` (interp) reach it; both carry
same-kind scalar fast paths above it. `Region::Equal` in the two dispatch
lowerings compares against a constant and goes through the same function.

**Ordering** — owner `cmp_any_value` / `fz_value_cmp_ref`
(`runtime/src/ir_runtime.rs`), shared since fz-5xp.18. `guard_cmp`
(`ir_interp/dispatch_exec.rs`) has integer and float fast paths and then
delegates; `fz_value_cmp_raw_const` exists so codegen can compare a ref against
an unboxed payload without allocating a scalar box. Two integers are ordered AS
INTEGERS — widening both to `f64` loses the distinction above 2^53. Ordering
between values of different kinds is not supported yet and panics loudly:
fz-5xp.8.

**Arithmetic** — no single owner, and that is deliberate. The typed shim NAMES
are the shared fact: `fz_op_add_ii`, `_if`, `_ff` and so on say which lanes they
take, so each door implements the same typed operation rather than re-deriving
which operation applies. Native lowers them in place (`ARITH_SHIMS` in
`native_codegen/prim.rs`); the interpreter has private Rust shims
(`ir_interp/extern_call.rs`). They agree because the name carries the types.
Float remainder is the known exception: fz-5xp.34.

**Runtime type tests** — owner `RuntimeTestAxis` (`src/runtime_type_predicate.rs`),
one axis table with three lowerings that must each be taught, and the design we
want everywhere. The claim held under audit, with one hole: an axis is a
question about a language VALUE, not a storage kind, and a binary has two
representations. `ValueKind::BINARY_REPRS` names them once so every lowering
reads the same fact (fz-5xp.57).

**Bitstring matching** — one runtime implementation, `fz_bs_read_field_bits`,
reached from every door. But the CLAUSE HEAD is lowered twice — once into a
dispatch region to select the clause, once into body steps to bind — so each
field is read twice: fz-5xp.56.

**Map key identity and order** — owner `runtime/src/heap/key_cmp.rs`. Order must
agree with equality, because a map is a flat sorted array: if two equal keys are
not adjacent, a dedup driven by the order never sees them collide and a binary
search misses what a linear scan finds (fz-5xp.48). Both raw writers
(`alloc_map_slots`, `alloc_map_refs_bits`) sort and dedup, so callers do not
pre-sort — `compiler2/source.rs` did, with a comparator that ordered binary keys
by address, and the result was discarded by the re-sort. A second authority
whose answer is thrown away is still a second authority.

**Binary representation** — owner `ValueKind::BINARY_REPRS`
(`runtime/src/any_value.rs`). Inline `Bitstring` below
`SHARED_BIN_THRESHOLD_BYTES`, shared-buffer `ProcBin` above it.

**Inline or shared storage** — owner `Heap::alloc_bitstring`, which returns the
VALUE rather than a pointer the caller re-classifies (fz-5xp.45). Two other
readings of the threshold remain and are different questions:
`alloc_bitstring_suffix` asks whether a VIEW is worth a stub, and native codegen
asks what to EMIT for a constant bitstring, which it must answer at compile time
with no heap to ask.

**Where a foreign symbol lives** — owner `fz_extern_symbol_addr`
(`runtime/src/extern_variadic.rs`). The interpreter's `resolve_symbol` fallback
and its variadic path call it, and the JIT is built with it as its
`symbol_lookup_fn` rather than cranelift's own dlsym. The AOT door is answered
by the linker instead, which is a fourth place and why `-lm` is hardcoded:
fz-5xp.61.

**Which runtime symbols exist, and their ABI** — owner `RUNTIME_SYMBOLS`
(`src/extern_contract.rs`). Reachability from compiled code is held by a test
rather than by construction, because an address table has to exist somewhere:
see `every_declared_runtime_symbol_is_reachable_from_compiled_code`.

## Reading this list

Two properties make an entry safe. The rule is stated once, and the places that
do not state it can only ASK. Where a door restates the rule — the Atom arm of
`emit_truthy_cmp`, `guard_cmp`'s numeric arms — the restatement is narrower than
the rule and cannot answer a case the owner would answer differently.

Where an entry names a ticket, that question currently has more than one answer
or an answer that is not yet complete. Adding a semantic predicate to fz means
adding a row here, not just an implementation.
