# Lazy Continuation Materialization

## Model

A continuation carries two ideas that the runtime keeps apart:

- control: the compiler-known code pointer plus the typed captures the next step
  needs to run;
- scheduler root: a heap closure a process can park, drag through GC, and resume
  later.

Most native calls only need the first. They run synchronously and never cross a
scheduler boundary, so codegen represents the continuation as a stack-backed
*lazy descriptor* instead of allocating a heap closure. The descriptor holds the
same code pointer and captures the next step would read from a closure, but lives
in a Cranelift stack slot owned by the producing frame. Materialization — turning
the descriptor into an ordinary heap closure — happens only when the continuation
escapes: returning it, storing it in heap data, sending it, parking it at a
scheduler boundary, or capturing it into another escaping closure. So a
continuation's representation is a codegen choice; whether it is a join point or
a scheduler root is the semantic fact.

The pieces that own each decision:

- `build_lazy_cont_descriptor` (`src/ir_codegen/closure.rs`) emits the stack-slot
  descriptor and returns a tagged word standing in for it.
- `build_cont_closure` (same file) emits the heap closure, and materializes any
  lazy captures on the way in so nothing lazy ends up on the heap.
- `ContinuationPlan` (`src/ir_codegen/terminator.rs`) chooses between the two per
  call site and emits the right call shape.
- `fz_materialize_cont` and the closure accessors (`runtime/src/ir_runtime.rs`)
  read both forms and convert a descriptor into a closure on demand.

## Runtime Shape

A lazy descriptor is not an `AnyValueRef`. Its word is a stack address tagged
with `TAG_FWD` (`runtime/src/any_value.rs:30`), the Cheney forwarding tag.
`emit_tagged_pointer_ref_word` (`src/ir_codegen/closure.rs:219`) shifts that tag
into the high tag field by `tag_shift` (56 on arm64/TBI, 57 on x86-64 canonical),
where `ValueKind::new` rejects it — so the word can never be mistaken for a real
value ref. `is_lazy_cont_ref` (`runtime/src/ir_runtime.rs:1786`) detects the
marker by shifting the same field back out and comparing to `TAG_FWD`.

The stack slot has a fixed 32-byte header (`LAZY_CONT_HEADER_BYTES`) followed by
two parallel arrays:

- offset 0: code pointer;
- offset 8: continuation spec id;
- offset 16: capture count;
- offset 32: one raw 8-byte word per capture;
- after the raw words: one kind byte per capture — `ref`, `i64`, `f64`, or
  `atom` (`LAZY_CONT_KIND_*`, `src/ir_codegen/closure.rs:167`,
  `runtime/src/ir_runtime.rs:1780`).

Capture 0 is always the descriptor's own outer continuation; user captures
follow, exactly the slot order a heap cont closure uses (`build_cont_closure`
reserves env field 0 for `outer_cont` the same way).

The closure accessors understand both forms. Each checks `is_lazy_cont_ref`
first; on a descriptor it reads straight from the stack slot, otherwise it
follows the heap closure:

- `fz_closure_code_ref`;
- `fz_closure_get_capture_ref`;
- `fz_closure_get_capture_i64`;
- `fz_closure_get_capture_f64`;
- `fz_closure_get_capture_atom`.

Because the accessors are dual, a continuation body needs no second ABI. It
receives its `self` word — descriptor or closure — and asks the runtime for
captures the same way either way.

Capture storage follows the *target continuation's entry ABI*, not the
producer's SSA shape. `ContinuationPayload::from_capture_vars`
(`src/ir_codegen/terminator.rs:163`) reads the cont spec's `param_reprs` and
`closure_capture_for_var_as` (`src/ir_codegen/value.rs:97`) coerces each captured
var to that repr. If the next step reads a capture with
`fz_closure_get_capture_i64`, the descriptor stores a raw `i64` slot even when
the producer holds an `AnyValueRef`. That keeps stack descriptors and
materialized heap closures observationally identical at the accessor boundary.

## Choosing The Representation

`ContinuationPlan` is `LazyNativeDescriptor` or `HeapClosure`. The continuation
must be native (`spec_is_native`) and emitted from a native body for a lazy
descriptor to be possible at all; a uniform-ABI body always builds a heap
closure. On top of that:

- For a direct `Term::Call` / `Term::TailCall` the gate is
  `cont_can_use_lazy_descriptor = !closure_capture_counts.contains_key(callee)
  && !cont_captures_callable` (`src/ir_codegen/terminator.rs:703`). A callee that
  expects a real closure `self`, or a continuation that captures a callable value
  the runtime cannot resolve to a thin `KnownFn`, forces a heap closure.
- For `Term::CallClosure` / `Term::TailCallClosure` the gate is just
  `is_native && cont_is_native` (`src/ir_codegen/terminator.rs:1140`). The
  conservative callable-capture rule is unnecessary here: the closure call passes
  its hidden continuation only as the callee's continuation argument, never into
  user data, and the dual accessors plus `fz_materialize_cont` handle a
  descriptor wherever that argument flows.

`closure_call_lowered` telemetry (`src/ir_codegen/terminator.rs:1148`) records
`continuation_storage` as `lazy_descriptor` or `heap_closure` for each lowered
closure call, alongside `dispatch_kind` (`direct` for a resolved closure-lit
body, `indirect` for the code-pointer seam).

`cont_captures_callable` is decided by `capture_forces_heap_continuation`
(`src/ir_codegen/terminator.rs:1076`): a capture forces a heap continuation when
it is callable-typed (`callable_clauses` is `Some`) and its
`SpecPlan.callable_capabilities` entry is anything other than `KnownFn`. The
three capabilities differ in runtime state: `KnownFn(FnId)` is a thin function
ref with no closure word, so it does not push caller continuations onto the heap;
`KnownClosure { .. }` and `OpaqueCallable` carry runtime callable state and must
stay closure-shaped values when threaded through user data
(`src/ir_planner/fn_types.rs:76`).

## Heap Escape: Materialize On The Way In

A descriptor may not be written into heap data: heap closure captures are
GC-visible `AnyValueRef` slots, and a stack descriptor is neither a value nor a
GC root. `build_cont_closure` enforces this. Before storing its outer
continuation or any ref capture, it calls `fz_materialize_cont`
(`src/ir_codegen/closure.rs:130`,`:134`). Ordinary refs pass through unchanged;
a descriptor is rebuilt as a heap closure, and `fz_materialize_cont` recurses on
each `ref` capture (`runtime/src/ir_runtime.rs:1832`), so a tree of nested lazy
continuations becomes fully scheduler-safe before any of it can escape.

The scheduler boundary is the other escape. `emit_back_edge_yield_check`
(`src/ir_codegen/terminator.rs:997`) spends one reduction on every native loop
back-edge; when reductions hit zero it builds a real heap closure for the parked
work and runs the threaded continuation root through `materialize_cont`
(`src/ir_codegen/terminator.rs:1057`) before handing it to
`fz_yield_mid_flight_report`. Parked runnable work the scheduler sees is always a
normal typed closure.

## Stack Lifetime: Pass With call, Not return_call

The frame that owns a descriptor must stay live while the callee may read it. So
a call passing a freshly built descriptor uses `call` (or `call_indirect`)
followed by `return`, never `return_call`/`return_call_indirect`: a tail call
would pop the very frame that owns the stack slot. The same call shape used for a
heap-closure continuation is a tail call, because a heap closure outlives the
frame.

`emit_call`/`emit_tail_call` select on `uses_lazy_cont`
(`src/ir_codegen/terminator.rs:750`); the closure-call paths select on
`can_use_lazy_cont` (`src/ir_codegen/terminator.rs:1175`,`:1210`). When a body
that captures the continuation as a heap closure tail-calls, the descriptor never
existed, so the tail call is safe.

## Relationship To Destination Planning

This is a representation choice layered on top of facts the planner already owns.
The planner fixes call-edge semantics through `SpecPlan.call_edges` and the
return contract, and local container construction stays explicit destination IR.
Lazy continuation materialization changes none of that: for a compiler-known
native continuation it only decides whether the agreed typed captures ride a
stack slot or a heap closure until a boundary forces the closure.

## Walkthrough

A native body finishes work and hands control to its compiler-known native
continuation `k`, then a synchronous native callee:

```text
k = stack_descriptor(code_ptr, cont_sid, captures...)   # TAG_FWD word
result = call callee(args, k)        # call, not return_call: our frame owns k
return result
```

If `callee` parks at a scheduler boundary, the yield path turns `k` into a heap
closure first:

```text
reductions_remaining == 0:
  heap_k = materialize(k)            # stack slot -> GC-visible closure
  yield mid-flight with heap_k
```

If `k` instead escapes into another continuation closure, `build_cont_closure`
materializes it as it stores the capture, so the heap never holds a `TAG_FWD`
word.

## Tests

The fixture matrix pins the model. Each gate states a contract:

- `quicksort` — native JIT/AOT allocates zero continuation closures on a purely
  list-building recursion: `closure_allocs = 0`, `closure_bytes = 0`,
  `list_cons_bytes = 176`, total `bytes = 176`.
- `enum_list_allocations` — the runtime-library list-consumer floor for
  compiler-known native higher-order calls: `list_cons_allocs = 5`,
  `list_cons_bytes = 80`, `closure_allocs = 1`, `closure_bytes = 32`. Its native
  CLIF gate also checks that the known list receiver statically dispatches to
  `Enumerable.List.reduce/3` (no `call_indirect`), which delegates to local
  `List.reduce_cont/3` (kept in `return_call` tail form). That is the model
  boundary: protocol dispatch selects the implementation once, and a real
  user-supplied reducer stays a source-visible closure value.
- `enum_reduce_suspend` — the paired negative gate. A returned suspend function
  is a source-visible value, not an internal continuation edge, so native
  JIT/AOT allocates one real heap closure (`closure_allocs = 1`).
- `append`, `reverse`, `filter` — list-building native paths that must keep
  continuation closures off the heap.

A `closure_call_lowered` telemetry assertion (the `opaque_fn_value_join` path)
proves an indirect reducer continuation stays a `lazy_descriptor` while its
reducer call lowers through the protocol-dispatched list reducer without forcing
heap continuation allocation.
