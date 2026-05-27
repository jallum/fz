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
if should_yield:
  k = materialize(lazy_cont)
  yield_mid_flight(k)
```

That keeps scheduler and GC machinery simple: parked runnable work is still a
normal typed closure.

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
`SpecPlan.return_uses`, `SpecPlan.return_context_plans`, and
`SpecPlan.dispatches`.

The lazy descriptor is a representation choice after those facts are known:
for a compiler-known native continuation, codegen can carry the same typed
capture facts on the stack until a scheduler boundary forces heap materializa-
tion.

## Proof Gates

Use these gates when touching lazy continuation materialization:

- `cargo test --test fixture_matrix quicksort`
- `cargo test --test fixture_matrix append`
- `cargo test --test fixture_matrix reverse`
- `cargo test --test fixture_matrix filter`

Quicksort's native JIT/AOT fixture pins the core signal:

```text
closure_allocs = 0
closure_bytes = 0
list_cons_bytes = 768
heap_bytes = 768
```
