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

The corollary is that there is exactly one such plan. See
[`single-authoritative-plan.md`](single-authoritative-plan.md) for why
`compile_with_backend_impl` derives the authoritative plan once (no second plan
to reconcile, no telemetry-silenced re-derivation), how the pre-plan transforms
read a capability slice instead of a full plan, and why destination lowering
needs no re-plan.

## Planner Vocabulary

The phase that produces these facts is `ir_planner::plan_module`. Its products
are deliberately broader than type maps:

- `SpecPlan` is one specialization's plan. It owns Var and block-env types,
  callable capabilities, dispatch choices (`call_edges`, which carry the
  return-use and return-context facts), reachable blocks, dead-branch facts, and
  extern-marshal facts.
- `ModulePlan` is one module's plan. It owns the specialization plans, effective
  returns, any-key indexes, precedence, effect summaries, cross-spec dead
  branches, and no test-only witness artifacts.

Local type-inference vocabulary stays narrow where the code is literally type
inference: `type_fn`, `Ty`, `vars`, block environments, and the narrowing and
concrete-type helpers keep their type-specific names. A plan is more than the
types it carries; the planner names match that scope.

## Authoritative Facts

`SpecPlan.call_edges` is keyed by `CallsiteId`: `(caller FnId, intrinsic
CallsiteIdent, EmitSlot)`. The value is a `CallEdgePlan`, which names the
selected target capability plus the return-use and return-context facts for that
edge.

`plan_module` reads structured `type_infer` activation return facts as
production data and projects them into the committed planner return cache. This
is data flow, not telemetry scraping.
`ActivationKey` and `SpecKey` are intentionally not the same concept:
activation facts are matched to planner keys by `FnId` and semantic input-slot
coverage. `ReturnDemand` is a delivery capability, not a semantic return
payload, so it does not split activation return facts. A known activation fact
may serve a planner key only when the activation input domain covers the
requested input domain. Concrete closure identity may be erased for this
comparison so a concrete captured reducer can satisfy the planner's
callable-capture slot without making closure identity an ABI fact.

Unresolved activation facts are retained both as exact boundary facts and as
overlap guards. An exact unresolved fact can be projected at the final boundary
(`Pending`/`Unknown` erase to `any` there), but a different known fact is not
projected for a requested key when any unresolved activation domain for the same
`FnId` overlaps that requested domain. This is deliberately key-sensitive:
unsettled `f(nonempty_list(int))` blocks a broad `f(list(int))` result, but it
does not poison disjoint facts for the same function. The planner does not
quarantine an entire `FnId` because one polymorphic call site is still
unsettled.
The `fz.planner.planned` event reports this activation projection with
`type_kernel: "activation"` plus activation return fact/key counts, entry
completion/unresolved/invalid counts, known/unresolved/no-return counts,
projected return count, projection-gap count, and the
`activation_return_projection_gaps` key list for any reachable specs the
activation facts cannot cover.

Local direct, closure, and continuation call edges target a `SpecKey`, which
names the callee function, its semantic input key, and its `ReturnDemand`.
Provider-boundary and protocol targets ride the same `CallEdgePlan` shape.

Imported module calls use that provider-boundary shape. Before link, the
IR carries an `ExternalCallEdge` and the call edge names the target `ExportKey`
plus the public input and demand selected upstream. `link_ir_units`
remaps unit-local facts into linked ids and resolves the provider-boundary
target to the local `SpecKey` while `Module::rewrite_external_calls_for_lto`
rewrites the terminator.

The synthetic `__external__.*` stub is only a lowering anchor. If a callsite has
an `ExternalCallEdge`, planner discovery records a provider-boundary
`CallEdgeTarget::External`; it must not plan through the stub body or read the
stub's `external_module_unlinked` halt as a real return. Non-tail external
calls still get an ordinary local `Cont` edge. The continuation's slot-0 type
comes from the callee's public `@spec` when available, otherwise from `any`,
because an unknown provider result is a complete boundary fact, not a pending
local return.

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
- `ClosureCall` names a closure-call callsite. It is purely structural — it
  identifies where the closure dispatch happens, while the call edge's target
  shapes what runs, whether that comes from a known callable capability or a
  closure literal clause.
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

Call-edge facts consume callable capabilities alongside the return contract: the
target says what code may run, and the return contract pairs that exact target
with the executable strategy that makes the caller's result context legal. The
same fact gates continuation representation; see the callable-capability gate in
[`lazy-continuation-materialization.md`](lazy-continuation-materialization.md).

Known-target closure rewriting is an all-spec consensus rule over these same
facts. A threaded callable parameter can be rewritten to a direct zero-capture
function only when every specialization of the enclosing function that has a
callable fact agrees on the same `KnownFn`. `KnownClosure` and
`OpaqueCallable` are not absence of evidence; they are positive evidence that
runtime callable state may exist, so they poison the consensus. Ignoring those
facts makes the first zero-capture reducer that reaches a higher-order function
globally replace later captured reducers, which is unsound.

## Return Demand Is A Variant Capability

`SpecKey.demand` is part of the dispatch target. That means return-demand
destination planning uses the same mechanism as ordinary variant selection:
the planner selects a compile-time capability, then codegen emits the ABI and
body for exactly that capability.

The executable call-edge fact is `ReturnContract`: it contains the selected
local target `SpecKey` including demand and a `ReturnStrategy`. Ordinary value
returns use `ReturnStrategy::Value`; tuple-field returns use
`ReturnStrategy::TupleFields(N)`; list-tail returns carry the matching
`ReturnContextPlan` inside `ReturnStrategy::ListTail` or
`ReturnStrategy::TupleFieldsListTail`, except for tail calls that forward the
caller's demanded ABI directly with `ReturnStrategy::ForwardedDemand`. The
strategy's demand must match the target demand. A demand without the matching
strategy is an unknown/incomplete plan, not a usable fact.

Native codegen lowers from the contract payload. It does not rediscover
list-tail lanes from captures or treat tuple-field return demand as an entry
parameter rewrite for ordinary functions. Tuple-field entry expansion is only
for continuation functions that receive a producer's tuple fields directly; a
plain function with `ReturnDemand::TupleFields(N)` keeps its normal entry
parameters and only changes how its return is delivered.

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

This delivery capability is not the same fact as the chain's terminal halt
kind. `ReturnDemand` answers "how does this result cross the immediate seam?"
while declared/effective return payloads answer "what values can eventually
emerge if the chain halts?" A `Value`-demanded native spec therefore delivers a
boxed value ref even when its reachable payload set is a singleton int or
float. The halt side may still use a narrower kind when the reachable return
chain proves one.

Choosing a function variant, choosing a tuple-return ABI, and choosing a
return-context body are the same kind of decision: a typed callsite capability
selected before codegen.
Protocol implementation selection is the same kind of decision: the planner
selects a static-direct (`ProtocolDispatch::Local`), provider-boundary
(`ProtocolDispatch::External`), or diagnostic edge from receiver type facts and
visible implementation-domain facts. Finite-union receiver domains are rewritten
before execution into `TypeTest` / `If` cascades with direct-call arms for each
visible local implementation; named source structs are tested by schema id, and
kinded containers such as lists and maps are tested by value kind. Open or
erased receiver domains keep a final protocol-stub fallthrough for any residual
non-implementing shape; no runtime lookup table is emitted.

Protocol callback callsites lower to ordinary call-shaped IR with a protocol
stub callee. The stub is not the semantic target. It is a stable callsite
anchor that lets the planner publish a `CallEdgePlan` to the selected local
implementation or to a provider-boundary `ExportKey`; linking then remaps that
edge and rewrites the callsite when the provider body becomes available.
Single-unit frontend checking performs the same rewrite for local planned
targets before interpreter or native execution, using the planner fact rather
than rediscovering the protocol target in a backend.

There are two frontend rewrite cases:

- Static-single: every reachable caller specialization that mentions the same
  physical `CallsiteId` selects the same local target. The frontend can rewrite
  that shared IR callsite to the agreed target.
- Switch-union: specializations of the same physical callsite select different
  local protocol targets. The frontend must leave the protocol stub in place so
  closed-union protocol dispatch can rewrite it into a `TypeTest` / `If`
  cascade with one direct-call arm per implementation.

The agreement check is required because a physical callsite is shared by all
monomorphized specs of its caller. Rewriting it per spec would make the last
planned target win globally, collapsing a polymorphic protocol call such as
`Enum.count/1` onto one implementation and erasing the switch-dispatch anchor.

The crucial invariant: demand follows a specific return edge/result hole, not
the whole caller spec. A caller spec may contain multiple calls, and each call
can feed a different use. Codegen must therefore consume the `CallsiteId` facts
the planner produced instead of reusing the caller spec's demand as a blanket
property.

Effective returns in the committed `ModulePlan` are a projection/cache of
activation facts over the reachable executable specs. `Known(T)` projects to
`T`, `NoReturn` projects to `none`, and residual `Pending`/`Unknown` project to
`any` only at this boundary. Specs that remain reachable without a compatible
activation fact are reported as projection gaps; they are not silently justified
by the planner's discovery-time return fixpoint. Zero projection gaps is the
acceptance signal that the committed executable plan is covered by activation
facts.

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

Native lowering also consumes `SpecPlan.reachable_blocks`. A native spec emits
only blocks reachable for that spec; an `If` whose other successor is
spec-unreachable lowers as a direct jump to the live successor. This is still
planner output, not a backend guess: the same branch narrowing that publishes
reachable blocks is responsible for preserving non-list values on predicates
such as `not IsEmptyList(x)`.

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
