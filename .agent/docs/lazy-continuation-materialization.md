# Lazy Continuation Materialization

## Model

A continuation has two separate meanings:

- control: the compiler-known code pointer plus typed captures needed to run
  the next step;
- scheduler root: a heap closure the process can park, move through GC, and
  resume later.

Most native calls only need the first meaning. They run synchronously and do
not cross a scheduler boundary. In that case codegen uses a stack-backed lazy
continuation descriptor instead of allocating a heap closure.

```text
call append(xs, ys, lazy_cont)
  append may read lazy_cont like a closure
  no scheduler boundary happens
  no closure is allocated
```

If execution reaches a real yield edge, the lazy descriptor is materialized into
an ordinary closure before the scheduler sees it:

```text
if reductions_remaining <= 0:
  k = materialize(lazy_cont)
  yield_mid_flight(k)
```

That keeps scheduler and GC machinery simple: parked runnable work is still a
normal typed closure.

This applies to known higher-order calls too. If `Term::CallClosure` resolves
to one known native closure body, codegen resolves the target before building
the continuation value. The reducer body still receives a closure-shaped `self`
word for its continuation, but that word can be a stack-backed lazy descriptor
instead of a heap closure.

## Runtime Shape

Lazy descriptors are not `AnyValueRef`s. They use the invalid high-bit
`TAG_FWD` ref tag as a compiler-private marker, with the address payload
pointing at an explicit Cranelift stack slot.

The descriptor stores:

- code pointer;
- continuation spec id;
- capture count;
- raw capture words;
- one kind byte per capture (`ref`, `i64`, `f64`).

The ordinary closure accessors understand both forms:

- `fz_closure_code_ref`;
- `fz_closure_get_capture_ref`;
- `fz_closure_get_capture_i64`;
- `fz_closure_get_capture_f64`.

This is deliberate. Continuation bodies do not need a second ABI. They receive
their `self` word and ask the runtime for captures exactly as before.

## Heap Escape Rule

A lazy descriptor may not be written into heap data. Heap closure captures are
GC-visible `AnyValueRef` slots; a stack descriptor is neither a value nor a GC
root.

When `build_cont_closure` stores an outer continuation or a ref capture, it
first calls `fz_materialize_cont`. Ordinary refs pass through unchanged. Lazy
descriptors become heap closures recursively, so anything that escapes into a
heap closure is scheduler-safe.

## Stack Lifetime Rule

The frame that owns a lazy descriptor must remain live while the callee may use
that descriptor. Therefore a call that passes a freshly built lazy descriptor
uses normal `call` plus `return`, not `return_call`.

Bad:

```text
descriptor = stack_descriptor(...)
return_call callee(args, descriptor)
```

The tail call can remove the stack frame that owns `descriptor`.

Good:

```text
descriptor = stack_descriptor(...)
result = call callee(args, descriptor)
return result
```

## Destination Planning Boundary

Lazy continuation materialization is not destination planning. The planner still
owns destination semantics through `SpecKey.demand`,
`SpecPlan.call_edges`.

The lazy descriptor is a representation choice after those facts are known:
for a compiler-known native continuation, codegen can carry the same typed
capture facts on the stack until a scheduler boundary forces heap materializa-
tion.

## Callable Capability Gate

Callable-typed caller state is a lazy-descriptor barrier only when it carries
runtime callable state. `SpecPlan.callable_capabilities` lets codegen distinguish
these cases:

- `KnownFn` has no runtime closure state and does not, by itself, force caller
  continuations onto the heap.
- `KnownClosure` and `OpaqueCallable` remain conservative barriers because they
  either carry captured state or cross a callable boundary the current spec
  cannot name precisely.

Continuation captures are still checked conservatively from their callable type.
A captured callable becomes scheduler-visible if the continuation materializes,
so zero-state capture relaxation must wait until the runtime reduce/resume
carrier bug tracked by `fz-pu9` is fixed.

## Proof Gates

Use these gates when touching lazy continuation materialization:

- `cargo test --test fixture_matrix quicksort`
- `cargo test --test fixture_matrix enum_list_allocations`
- `cargo test --test fixture_matrix enum_reduce_suspend`
- `cargo test --test fixture_matrix append`
- `cargo test --test fixture_matrix reverse`
- `cargo test --test fixture_matrix filter`

Quicksort's native JIT/AOT fixture pins the core signal:

```text
closure_allocs = 0
closure_bytes = 0
list_cons_bytes = 176
heap_bytes = 176
```

`enum_list_allocations` pins the runtime-library list-consumer floor for known
native higher-order calls:

```text
list_cons_allocs = 5
list_cons_bytes = 80
closure_allocs = 0
closure_bytes = 0
```

`enum_reduce_suspend` is the paired negative gate. A returned suspend function
is a source-visible value, not an internal continuation edge, so native JIT/AOT
must still allocate one real heap closure there.
