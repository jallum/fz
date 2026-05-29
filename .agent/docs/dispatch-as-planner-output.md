# Dispatch As Planner Output

The compiler treats dispatch decisions as typed facts produced by the planner.
Codegen consumes those facts; it does not re-derive them from names, source
spans, or best-effort local type reconstruction.

Source calls, closure calls, continuation hops, recursive back edges, and
scheduler suspension have different runtime shapes, but the planner models them
all as state transitions over facts it already records — call-edge targets,
return-context plans, and callable capabilities. Passes read those facts rather
than reconstructing control shape from closure frames or capture order.

Destination planning is the main application of this rule. See
[`destination-passing.md`](destination-passing.md) for the
container construction model, `ReturnDemand` composition, and return-context
plans.

Protocol dispatch uses the same rule. See [`protocols.md`](protocols.md) for
the protocol-domain type contract, implementation target identity, dispatch
outcomes, and the requirement that link/load stages preserve planner facts
instead of reconstructing them with a second planning pass.

## Planner Vocabulary

The phase that produces these facts is `ir_planner::plan_module`. Its products
are deliberately broader than type maps:

- `SpecPlan` is one specialization's plan. It owns Var and block-env types,
  dispatch choices (`call_edges`), return-use and return-context facts,
  reachable blocks, dead-branch facts, function-constant facts, physical
  capabilities, and extern-marshal facts.
- `ModulePlan` is one module's plan. It owns the specialization plans, effective
  returns, any-key indexes, precedence, effect summaries, SCC facts, cross-spec
  dead branches, and closure handles.

Local type-inference vocabulary stays narrow where the code is literally type
inference: `type_fn`, `Ty`, `vars`, block environments, and the narrowing and
concrete-type helpers keep their type-specific names. A plan is more than the
types it carries; the planner names match that scope.

## Authoritative Facts

`SpecPlan.call_edges` is keyed by `CallsiteId`: `(caller FnId, intrinsic
CallsiteIdent, EmitSlot)`. The value is a `CallEdgePlan`, which names the
selected target capability plus the return-use and return-context facts for that
edge.

Local direct, closure, and continuation call edges target a `SpecKey`, which
names the callee function, its semantic input key, and its `ReturnDemand`.
Provider-boundary and protocol targets ride the same `CallEdgePlan` shape.

Imported module calls use that provider-boundary shape. Before link, the
IR carries an `ExternalCallEdge` and the call edge names the target `ExportKey`
plus the public input and demand selected upstream. `link_ir_units_with_plan`
remaps unit-local facts into linked ids and resolves the provider-boundary
target to the local `SpecKey` while `Module::rewrite_external_calls_for_lto`
rewrites the terminator.

Each call edge may also record the typed return-use fact for its result hole and
the executable plan for return-use facts that need lowering. The current
concrete plans lower ListTail contexts. They can also name the already-proved
empty-tail continuation target used to preserve material value semantics without
a backend sibling probe.

This is per caller spec. The same syntactic callsite can dispatch to different
targets in different caller specializations, so a module-global callsite table
is not precise enough.

That same precision applies to return-context plans: plan operands are typed
facts for one caller specialization, not backend observations about continuation
capture order.

`EmitSlot` separates the facts produced by one call-shaped terminator:

- `Direct` names the direct callee body.
- `Cont` names the continuation body.
- `ClosureCall` names a closure invocation target when the closure type carries
  enough compile-time identity.
- `MakeClosure` names the body spec made reachable by constructing a closure
  value.

## Callable Capabilities

`SpecPlan.callable_capabilities` carries callable identity as value-capability
data:

```text
CallableCapability =
  KnownFn(fn_id)
  KnownClosure { fn_id, captures }
  OpaqueCallable
```

The names describe what the compiler knows about a value, not which runtime
object must be built:

- `KnownFn` is a direct code identity with no runtime closure state. It can come
  from a zero-capture closure literal, but the useful fact is "this value can be
  called as this function," not "this value is a closure." The module inliner
  uses this: direct callsites to a `KnownFn` target can inline even when a
  zero-state closure value for the same function also exists elsewhere.
- `KnownClosure` is a direct code identity plus captured runtime state. It
  supports direct call edges, but the captures are real state and stay a
  representation barrier; the inliner keeps these targets callable as closure
  entries.
- `OpaqueCallable` is a callable boundary whose concrete target is not a single
  known function in this plan — for example, control flow that joins several
  zero-capture function values. It keeps the indirect-call shape and the
  conservative materialization rules, and is not collapsed to one static
  identity.

Call-edge facts consume callable capabilities alongside the return context: the
target says what code may run, and the return context says how the result
becomes the next state. The same fact gates continuation representation; see the
callable-capability gate in
[`lazy-continuation-materialization.md`](lazy-continuation-materialization.md).

## Return Demand Is A Variant Capability

`SpecKey.demand` is part of the dispatch target. That means return-demand
destination planning uses the same mechanism as ordinary variant selection:
the planner selects a compile-time capability, then codegen emits the ABI and
body for exactly that capability.

`ReturnDemand` has two axes:

- delivery: `Value` or `TupleFields(N)`;
- context: `None` or `ListTail(tail_ty)`.

Rendered capabilities are:

- `Value`: ordinary material return.
- `TupleFields(N)`: tuple field delivery to a continuation.
- `ListTail(tail_ty)`: hidden list-tail destination parameter.
- tuple field delivery plus ListTail context: tuple field delivery with a
  carried list-tail destination for product contexts, rendered as
  `tuple_fields(N, list_tail(tail_ty))`.

Choosing a function variant, choosing a tuple-return ABI, and choosing a
return-context body are the same kind of decision: a typed callsite capability
selected before codegen.
Protocol implementation selection is the same kind of decision: the planner
selects a direct, provider-boundary, closed-switch, runtime, or diagnostic edge
from receiver type facts and visible implementation-domain facts.

Protocol callback callsites lower to ordinary call-shaped IR with a protocol
stub callee. The stub is not the semantic target. It is a stable callsite
anchor that lets the planner publish a `CallEdgePlan` to the selected local
implementation or to a provider-boundary `ExportKey`; linking then remaps that
edge and rewrites the callsite when the provider body becomes available.
Single-unit frontend checking performs the same rewrite for local planned
targets before interpreter or native execution, using the planner fact rather
than rediscovering the protocol target in a backend.

The crucial invariant: demand follows a specific return edge/result hole, not
the whole caller spec. A caller spec may contain multiple calls, and each call
can feed a different use. Codegen must therefore consume the `CallsiteId` facts
the planner produced instead of reusing the caller spec's demand as a blanket
property.

## Why Not Re-Walk In Codegen

Post-planner passes may move, fold, or delete blocks. They must not invent new
call shapes after the planner commits to specs. `CallsiteIdent` survives legal
moves, and `SpecPlan.call_edges` remains the precise mapping from each
surviving call shape to its selected capability.

Re-walking in codegen is wrong for three reasons:

- it can miss per-spec facts, because one caller spec's block environment is not
  another caller spec's block environment;
- it can choose a body that the `SpecRegistry` did not register;
- it can silently diverge from effective-return propagation and continuation
  ABI selection.

The invariant is simple: if codegen sees a direct or continuation callsite, the
current caller's `SpecPlan.call_edges` must contain the selected local
`SpecKey`. Missing entries are compiler bugs. If codegen lowers return-demand
behavior, the corresponding return-use or return-context plan must also come
from that call edge. Backend closure captures and CLIF parameter shapes are
implementation details, not proof sources, and codegen must not construct
alternate demanded `SpecKey`s.

For provider-boundary rewrites, the linked callsite must still be the same
call: same caller, same callsite identity, and same target arity. The arity
check keeps source-span collisions from rewriting a matcher branch or recursive
tail call to an unrelated imported function.

## Return-Demand Boundaries

ReturnDemand capabilities are semantics-preserving only under the proof that
created them.

`TupleFields` is local product decomposition: the callee returns fields instead
of allocating a tuple struct, and the continuation receives those fields in the
same order.

The proof is local to that callee-to-continuation edge. A continuation compiled
to receive tuple fields may still tail-call another function using its captured
outer continuation; that outgoing tail call must not inherit the tuple-field
input shape unless a separate proof selected it for that edge.

`ListTail` is typed context passing. It can reorder pure recursive list work
only when the context proof does not cross observable operations. The effect
legality gates reject extern calls, scheduler-visible operations, receives,
closure calls, and allocation-stat readers such as
`Process.heap_alloc_stats()`.

Value-context ListTail lowering uses the same rule. When a material value can
be built by using an empty hidden list tail, the planner records that target in a
return-context plan. Codegen consumes the plan; it does not search for a
demanded sibling.

For quicksort, the selected capabilities make the typed context equivalent to:

```text
qsort_into(xs, tail)
```

The result remains an immutable list. The compiler imports the defunctionalized
context idea from FP2/TRMReC; it does not import destructive update.
