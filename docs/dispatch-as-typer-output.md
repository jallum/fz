# Dispatch As Typer Output

The compiler treats dispatch decisions as typed facts produced by the typer.
Codegen consumes those facts; it does not re-derive them from names, source
spans, or best-effort local type reconstruction.

## Authoritative Facts

`FnTypes.dispatches` is keyed by `CallsiteId`: `(caller FnId, intrinsic
CallsiteIdent, EmitSlot)`. The value is a `SpecKey`, which names the callee
function, its semantic input key, and its `ReturnDemand`.

This is per caller spec. The same syntactic callsite can dispatch to different
targets in different caller specializations, so a module-global callsite table
is not precise enough.

`EmitSlot` separates the facts produced by one call-shaped terminator:

- `Direct` names the direct callee body.
- `Cont` names the continuation body.
- `ClosureCall` names a closure invocation target when the closure type carries
  enough compile-time identity.
- `MakeClosure` names the body spec made reachable by constructing a closure
  value.

## Return Demand Is A Variant Capability

`SpecKey.demand` is part of the dispatch target. That means return-demand
destination passing uses the same mechanism as ordinary variant selection:
the typer selects a compile-time capability, then codegen emits the ABI and
body for exactly that capability.

Current demand capabilities are:

- `Value`: ordinary material return.
- `TupleFields(N)`: tuple field delivery to a continuation.
- `ListTail(tail_ty)`: hidden list-tail destination parameter.
- `TupleFieldsListTail(N, tail_ty)`: tuple field delivery plus a carried
  list-tail destination for product contexts.

This shape leaves room for future dispatch work. Choosing a function variant,
choosing a tuple-return ABI, and choosing a ListTail body are all the same kind
of decision: a typed callsite capability selected before codegen.

## Why Not Re-Walk In Codegen

Post-typer passes may move, fold, or delete blocks. They must not invent new
call shapes after the typer commits to specs. `CallsiteIdent` survives legal
moves, and `FnTypes.dispatches` remains the precise mapping from each surviving
call shape to its selected `SpecKey`.

Re-walking in codegen is wrong for three reasons:

- it can miss per-spec facts, because one caller spec's block environment is not
  another caller spec's block environment;
- it can choose a body that the `SpecRegistry` did not register;
- it can silently diverge from effective-return propagation and continuation
  ABI selection.

The invariant is simple: if codegen sees a direct or continuation callsite, the
current caller's `FnTypes.dispatches` must contain the selected `SpecKey`.
Missing entries are compiler bugs.

## Return-Demand Boundaries

ReturnDemand capabilities are semantics-preserving only under the proof that
created them.

`TupleFields` is local product decomposition: the callee returns fields instead
of allocating a tuple struct, and the continuation receives those fields in the
same order.

`ListTail` is typed context passing. It can reorder pure recursive list work
only when the context proof does not cross observable operations. The effect
legality gates reject scheduler-visible operations, receives, closure calls,
observable externs, and allocation-stat readers such as
`Process.heap_alloc_stats()`.

For quicksort, the selected capabilities make the typed context equivalent to:

```text
qsort_into(xs, tail)
```

The result remains an immutable list. The compiler imports the defunctionalized
context idea from FP2/TRMReC; it does not import destructive update.
