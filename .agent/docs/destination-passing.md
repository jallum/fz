# Destination Planning

Destination planning is the compiler decision that answers: where should this
value be built or delivered? Destination passing is one lowering technique for
that decision, used when an unpublished construction location or call context
has to be threaded through IR or an ABI.

A destination is an unpublished construction location; an init token is the
erased linear IR identity that proves which write/freeze operation may happen
next. Once a destination is frozen, the result is ordinary immutable data and
no later IR primitive may mutate it.

## Big Idea

The compiler should know where a value is going before it builds the value.
When the destination is typed, construction can happen directly in that context
without changing language semantics:

- a tuple result can be delivered as fields instead of as a temporary tuple
  that the caller immediately projects;
- a list prefix can be built in front of a known tail instead of built and then
  appended;
- a map literal or update can collect writes in unpublished storage and freeze
  once.

The simplifying rule is ownership of proof: the planner plans destinations and
dispatch choices, the IR carries explicit construction intent, and codegen
lowers those facts mechanically. Backend shape recognition is not proof.

There are two destination-planning families:

- init-token destinations in `fz_ir::Prim`, used for local tuple/list/map
  construction;
- return-demand destinations in `ir_planner::fn_types::ReturnDemand`, used when
  the planner proves that a call result can be delivered into a typed context
  without first materializing the ordinary return value.

Both families keep the same ownership rule: the compiler proves a private,
unpublished construction context, codegen lowers that context, and the
published result remains immutable.

Init tokens are not runtime values. They are compile-time facts attached to
`InitTokenId`, in the same broad family as:

- `Var -> Ty` facts in `SpecPlan.vars` and block environments.
- `CallsiteId -> CallEdgePlan` facts in `SpecPlan.call_edges`.
- `BlockId -> reachable/dead-branch` facts in `SpecPlan.reachable_blocks` and
  `SpecPlan.dead_branches`.
- `SpecKey.demand` facts such as tuple-field delivery and list-tail context.

The token fact is local to `ir_planner::type_fn`; it is not persisted in
`SpecPlan` because codegen needs only the final value type of ordinary vars.

For the broader dispatch rule that made this cleanup possible, see
[`docs/dispatch-as-planner-output.md`](../../docs/dispatch-as-planner-output.md).

## Return Demand

`SpecKey` includes a `ReturnDemand`. This is a typed compile-time capability,
not a runtime side channel. The planner chooses demanded variants while walking
specific callsites; codegen must implement the selected capability and must not
invent a different variant by guessing from function names.

`ReturnDemand` is factored into two axes:

- delivery: how the callee delivers the return value (`Value` or
  `TupleFields(N)`);
- context: what result context is already available at the return edge
  (`None` or `ListTail(tail_ty)`).

The central invariant is that demand follows a specific return edge/result
hole, not the whole caller spec. A caller spec can contain more than one call,
and different calls in that spec can have different return uses. The durable
facts are:

- `SpecPlan.call_edges`, keyed by `CallsiteId`, records the typed return-use
  fact and any executable return-context plan for each call edge.
  The return-context plans are present when a return-use fact needs lowering.
  The current concrete plans are ListTail plans: direct continuation delivery,
  nested cons-then-direct ListTail calls, tuple-field/list-tail continuation
  bridges, tail calls that forward a destination, and value-context
  continuations that use an empty hidden tail.

The caller `SpecKey` on a return-context plan is part of the proof. The same
syntactic callsite can be visited under multiple return contexts, so plan
operands must come from the current caller specialization rather than from a
callsite-only table or backend continuation capture order.

Return-context proof helpers live in `ir_planner::return_context`; the discovery
walker in `ir_planner::walk` should only call those helpers and record the
resulting facts. Keep new list-tail or tuple-field analyses in that helper
module unless they truly change traversal or worklist ownership.

Current rendered forms:

- `Value` is the ordinary material return.
- `TupleFields(N)` means a tuple result is delivered to the continuation as
  `N` Tail-CC values. This removes the tuple struct allocation for shapes such
  as `partition(...) -> {lo, hi}` when the continuation immediately projects
  the fields.
- `ListTail(tail_ty)` means the native callee receives a hidden physical list
  tail destination. Returning `[]` delivers that destination directly; returning
  a list literal builds its cons cells in front of the destination.
- `TupleFields(N)` delivery can compose with `ListTail(tail_ty)` context: the
  continuation receives tuple fields and also carries an appended hidden
  list-tail capture. This is rendered as
  `tuple_fields(N, list_tail(tail_ty))`.

`TupleFields(N)` is an input-delivery capability for the continuation that
immediately consumes the callee result. It does not leak through that
continuation into tail calls made with a captured outer continuation: at that
boundary the tuple-field proof has ended, so tail-call planning collapses the
tuple-field portion back to material `Value` delivery while preserving any
independently-proven `ListTail` context.

ListTail is the first typed return-context instance. For the source shape:

```text
append(qsort(lo), [pivot | qsort(hi)])
```

the demanded native path executes the equivalent context:

```text
hi_tail = qsort_into(hi, outer_tail)
pivot_tail = [pivot | hi_tail]
qsort_into(lo, pivot_tail)
```

This follows the FP2/TRMReC idea of making the evaluation context explicit and
defunctionalized, but it does not use destructive in-place mutation. Every cons
cell is still allocated as an immutable BEAM-style list cell on the owning
process heap; destination planning only chooses the tail that the new cells point
at.

Plain source-level structural code remains ordinary source code. The
`fixtures/append` fixture pins:

```text
append([1, 2, 3], [4, 5])
```

as a source `append/2` function, not an append BIF. Its native value path
allocates five cons cells: exactly the two input list literals. The copied
prefix is removed by owned-cons reuse rather than by a special append helper.
That fixture is an allocation baseline for library algorithms;
`fixtures/quicksort` is the return-context baseline that proves ListTail
context planning removes append-shaped rebuilding around recursive calls.

Return-context motion is legal only when the planner can prove that moving work
does not cross an observable barrier. The current gates reject contexts that
contain extern calls, scheduler-visible operations, receives, closure calls,
allocation-stats readers such as `Process.heap_alloc_stats()`, or halt.
Allocation by itself is not source-observable, but
allocation becomes observable in the presence of allocation-stat reads.

The pinned evidence is `fixtures/quicksort`: native JIT/AOT output keeps
`list_cons_allocs = 11`, `list_cons_bytes = 176`, `struct_allocs = 0`, and
headline `heap_bytes = 176`.

`fixtures/enum_sort` is the constant-callable return-demand baseline. The
default comparator is a zero-capture closure created inside the runtime library,
then threaded through `sort_list`, `fn_clause_2`, and `merge_sort_lists` under
both ordinary value demand and `ListTail` demand. Callable identity is
demand-independent: when the value is `KnownFn(F)` in every specialization and
the validation pass proves every occurrence is pure pass-through,
constant-closure elimination removes that dead parameter from the return-demand
specs as well, so the sorter never stays in a continuation frame to trip the
lazy-continuation materialization gate.

The native JIT/AOT evidence for `enum_sort` keeps `list_cons_allocs = 22`,
`closure_allocs = 0`, `scalar_box_allocs = 0`, and headline `heap_bytes = 352`.
Its static CLIF gate asserts that `sort_list`/`fn_clause_2`/`merge_sort_lists`
carry no constant-sorter signature (`&fn43[]`) and heap-allocate no
sorter-carrying continuations.

Owned-cons reuse is the next reduction layer. Multi-clause list destructuring
records a physical capability from a projected head back to the original source
cons cell. The source slot is not a source value and is not modeled as an
ignored semantic parameter. The spec dump exposes the capability:

```text
physical_capabilities:
  owned_cons_source param=Var(C) head=Var(H)
```

The physical parameter is not part of semantic specialization (`_` in the spec
key), but it gives native codegen the object-local capability needed to turn
`[h | new_tail]` into a reuse attempt for `C`. Native lowering consumes the
fact through one helper for `MakeList`, `DestListCons`, and `cons_then_direct`
ListTail return plans. That helper emits `fz_list_reuse_or_cons_tail_ref`.
The runtime alias bit remains the cell-local guard: if `C` is still unaliased,
the helper relinks it in place; if `C` was marked aliased, the helper allocates
a fresh cons with the same head and the requested tail. An aliased reuse
attempt is therefore an allocation miss, not a user-visible panic.

A source cons becomes ineligible for an owned reuse capability, or has its alias
bit set before reuse, when it is published outside the single owned rewrite path.
The publication barriers include closure and lazy-continuation capture that can
escape the current native activation, insertion into another heap container,
receive/scheduler-visible same-heap handoff, a non-tail call whose continuation
retains the same argument, halt, and allocation-stat reads that make allocation
timing observable.
Allocation alone is still not source-observable; crossing an observer is the
barrier.

Extern calls are not alias-publication boundaries for their arguments. An
extern that wants to retain a value after returning must copy it.

Send is different from same-heap publication. The runtime deep-copies messages
for cross-process send and self-send, so the sender's current-process cons
cells do not become aliased merely because they were sent. The destination
message graph is fresh in its heap; copied list cells must have clear alias
bits even if the source cells were already marked aliased.

## IR Vocabulary

`fz_ir::Prim` owns the destination operations:

- `DestTupleBegin { token, arity }` allocates an unpublished tuple destination
  and defines the first token.
- `DestTupleSet { dest, token, index, value, next }` consumes one token, writes
  one tuple field, and defines the next token.
- `DestFreeze { dest, token }` consumes the final tuple token and publishes the
  tuple value.
- `DestListBegin { token }` defines the first token for a destination-built
  list chain.
- `DestListCons { token, head, tail, next }` consumes one token, constructs one
  cons cell from `head` and a known tail, and defines the next token.
  `tail = None` means the empty-list sentinel.
- `DestListFreeze { list, token }` consumes the final list token and publishes
  the built list.
- `DestMapBegin { token, base, extra }` allocates an unpublished map
  destination. `base` seeds it from an existing immutable map for update-shaped
  construction; `extra` is the number of additional key/value writes.
- `DestMapPut { map, token, key, value, next }` consumes one token, sets one
  key/value pair in the unpublished map destination, and defines the next
  token.
- `DestMapFreeze { map, token }` consumes the final map token, canonicalizes
  the map ordering/deduplication, and publishes the immutable map value.

## Lowering

`ir_dest::lower_tuple_destinations` rewrites each surviving `MakeTuple` to:

```text
dest = DestTupleBegin(tok0, arity=N)
_    = DestTupleSet(dest, tok0, field=0, value=v0, next=tok1)
...
out  = DestFreeze(dest, tokN)
```

`ir_dest::lower_list_destinations` rewrites each surviving non-empty
`MakeList` from right to left:

```text
_  = DestListBegin(tok0)
c1 = DestListCons(tok0, head=b, tail=tail, next=tok1)
c0 = DestListCons(tok1, head=a, tail=c1, next=tok2)
xs = DestListFreeze(c0, tok2)
```

Empty-list literals remain the empty-list sentinel.

`ir_dest::lower_map_destinations` rewrites each surviving `MakeMap` or
`MapUpdate` to:

```text
m0  = DestMapBegin(tok0, base=base_or_none, extra=N)
_   = DestMapPut(m0, tok0, key=k0, value=v0, next=tok1)
...
out = DestMapFreeze(m0, tokN)
```

Runtime freeze preserves duplicate-key last-write-wins semantics while keeping
the published map canonical.

## Verification

`ir_dest::verify_module` owns structural correctness:

- token definitions are unique;
- each token is consumed at most once;
- tuple fields are in bounds and written at most once;
- tuple freeze requires every field to be initialized;
- tuple destinations are not written after freeze.

Tuple verifier transitions are factored through shared helpers in
`src/ir_dest.rs`; the planner uses those same transition helpers with `Ty`
payloads so verifier and planner do not drift.

## Typing

`ir_planner::type_fn` folds destination statements with erased token facts before
falling back to ordinary `type_prim` handling.

Tuple token facts carry initialized field slots. `DestFreeze` publishes
`Types::tuple(fields)` from the complete token fact, not from the opaque
destination handle type. This is what prevents tuple DP from turning
`partition(...) -> {lo, hi}` into `any`.

List token facts carry the current list value type. `DestListCons` still binds
the cons var to the precise non-empty list type, and `DestListFreeze` publishes
the token fact with a value-type fallback for malformed IR.

Map token facts carry the current map value type. `DestMapBegin` seeds the fact
from `base` or `Types::map(&[])`; `DestMapPut` refines static keys with
`var_as_map_key` and `Types::refine_map_field`; dynamic keys widen to
`map_top()`. `DestMapFreeze` publishes the token fact.

Malformed destination IR should not panic the planner. Verified codegen should
not see malformed IR, but the planner falls back conservatively (`any`, `nil`, or
the visible value type) and leaves diagnostics to the verifier.

## Runtime And GC

`ir_codegen` lowers tuple field writes through typed struct setters when local
representation facts prove raw int, float, or atom lanes. List destinations
lower to typed list-cons BIFs. Map destinations lower through
`fz_map_dest_begin`, `fz_map_dest_put_*`, and `fz_map_dest_freeze`; these helper
names are destination operations, not a separate language-level construction
model.

All destination storage lives in the process-private heap. GC safety comes from
ordinary roots: if a destination-built value is live across a call, receive, or
yield, it must be in normal frame/closure continuation state. Init tokens are
compile-time proof only; they are not scheduler state, closure captures, or
heap words.

Native continuations may be represented by stack-backed lazy descriptors while
execution stays synchronous. That does not change destination ownership:
destination facts still come from the planner, and a descriptor is materialized
into a normal closure before it can become scheduler-visible or heap-captured.
See
[`lazy-continuation-materialization.md`](lazy-continuation-materialization.md).

## Policy

Do not hide destination semantics only in codegen. Construction intent must be
visible in IR, verified, and typed through erased token facts. The native
JIT/AOT paths run `ir_dest::lower_destinations` before codegen. The `fz interp`
and scripted REPL fixture legs remain direct-IR baselines; they can execute
destination primitives when given already-lowered IR, but the CLI interpreter
does not apply the destination-lowering pass itself.

Do not make ReturnDemand a backend-only heuristic. `SpecPlan.call_edges` and
`SpecKey.demand` are the authoritative planner output. Codegen may lower only
those planner-authored ABI and context facts. It must not create a new demand
variant, probe demanded sibling specs, or infer demand from backend
closure/capture shapes.

Current deletion audit:

- no `TupleFieldsListTail` enum variant exists; tuple-field delivery plus
  ListTail context is represented by the two-axis `ReturnDemand`;
- `src/ir_codegen` no longer mutates dispatch keys with `key.demand = ...`;
- `src/ir_codegen/terminator.rs` no longer constructs demanded sibling
  `SpecKey`s with `ReturnDemand::list_tail` or
  `ReturnDemand::tuple_fields_list_tail`;
- `src/ir_codegen/terminator.rs` no longer recognizes ListTail context by
  indexing `continuation.captured[...]`.

Run destination lowering after the optimizer for now. Earlier lowering would
require every inliner/rewriter to remap init tokens correctly; post-optimizer
lowering keeps token ownership local to executable IR.

Do not resurrect broad same-function pre-DP fact merging. A previous quicksort
regression showed why: broad merging can attach facts to specs that DCE no
longer emits. The correct fix is preserving constructor precision through the
lowered IR with token facts.

## Proof Gates

Use these gates when touching destination planning:

- `cargo test ir_dest`
- `cargo test ir_planner`
- `cargo test tuple`
- `cargo test list`
- `cargo test map`
- `cargo test --test fixture_matrix quicksort`
- `cargo test --test fixture_matrix append`
- `cargo test --test fixture_matrix dump_budgets`
- `cargo clippy --workspace --all-targets -- -D warnings`
