# Dispatch As Typer Output

The compiler treats dispatch decisions as typed facts produced by the typer.
Codegen consumes those facts; it does not re-derive them from names, source
spans, or best-effort local type reconstruction.

## Authoritative Facts

`FnTypes.dispatches` is keyed by `CallsiteId`: `(caller FnId, intrinsic
CallsiteIdent, EmitSlot)`. The value is a `SpecKey`, which names the callee
function, its semantic input key, and its `ReturnDemand`.

`FnTypes.return_uses` is keyed by the same callsite identity. It records the
typed return-use fact for that edge. `FnTypes.list_tail_plans` is also keyed by
`CallsiteId`; it records the executable ListTail plan only for return-use facts
that need ListTail lowering. A ListTail plan can also name the already-proved
empty-tail continuation target used to preserve material value semantics
without a backend sibling probe.

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

`ReturnDemand` has two axes:

- delivery: `Value` or `TupleFields(N)`;
- context: `None` or `ListTail(tail_ty)`.

Current rendered capabilities are:

- `Value`: ordinary material return.
- `TupleFields(N)`: tuple field delivery to a continuation.
- `ListTail(tail_ty)`: hidden list-tail destination parameter.
- tuple field delivery plus ListTail context: tuple field delivery with a
  carried list-tail destination for product contexts, rendered as
  `tuple_fields(N, list_tail(tail_ty))`.

This shape leaves room for future dispatch work. Choosing a function variant,
choosing a tuple-return ABI, and choosing a ListTail body are all the same kind
of decision: a typed callsite capability selected before codegen.

The crucial invariant: demand follows a specific return edge/result hole, not
the whole caller spec. A caller spec may contain multiple calls, and each call
can feed a different use. Codegen must therefore consume the `CallsiteId` facts
the typer produced instead of reusing the caller spec's demand as a blanket
property.

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
Missing entries are compiler bugs. If codegen lowers return-demand behavior,
the corresponding return-use or ListTail plan must also come from `FnTypes`.
Backend closure captures and CLIF parameter shapes are implementation details,
not proof sources, and codegen must not construct alternate demanded `SpecKey`s.

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

Value-context ListTail lowering uses the same rule. When a material value can
be built by using an empty hidden list tail, the typer records that target in a
ListTail plan. Codegen consumes the plan; it does not search for a demanded
sibling.

For quicksort, the selected capabilities make the typed context equivalent to:

```text
qsort_into(xs, tail)
```

The result remains an immutable list. The compiler imports the defunctionalized
context idea from FP2/TRMReC; it does not import destructive update.
