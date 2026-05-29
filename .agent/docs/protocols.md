# Protocols

Protocols are typed implementation domains plus callback surfaces. The callback
surface says which functions an implementation must provide. The protocol
domain type says which values are known to have an implementation for that
protocol.

This is deliberately not the Elixir mechanism copied into fz. Elixir
`defprotocol` and `defimpl` expand through macros into modules and generated
dispatch functions, with consolidation rewriting implementation lookup for
speed. fz keeps the useful source shape, but the semantic object is a typed
compiler fact that can participate in planning, linking, diagnostics, and
representation choices.

## Source Contract

The source forms are:

```fz
defprotocol Enumerable do
  @spec reduce(t(a), b, (a, b) -> {:cont, b} | {:halt, b}) :: any
  fn reduce(enumerable, acc, reducer)
end

defimpl Enumerable, for: List do
  fn reduce(list, acc, reducer), do: Enumerable.reduce_list(list, acc, reducer)
end

defmodule Enum do
  @spec reduce(Enumerable.t(a), b, (a, b) -> {:cont, b} | {:halt, b}) :: any
  fn reduce(enumerable, acc, reducer), do: ...

  @spec sort(Enumerable.t(a)) :: [a]
  fn sort(enumerable), do: ...
end
```

`defprotocol` declares the protocol name, required callback names and arities,
public callback specs, and the protocol-domain type constructor
`Protocol.t(...)`.

`defimpl` declares the protocol it implements, the semantic implementation
target, and the callback bodies that satisfy the protocol.

The runtime library follows Elixir's public naming split: `Enumerable` is the
protocol identity and implementation-domain type, while `Enum` is the
convenience module that users call for enumeration operations. `Enum.sort/1`
and `Enum.sort/2` are ordinary runtime-library FZ functions implemented as a
stable merge sort over the list implementation.

`Protocol.t(...)` is not `any`. It is an implementation-domain constraint:
a value of type `Enumerable.t(a)` is a value for which an `Enumerable`
implementation is known. A concrete element argument refines the domain: the
protocol's domain template carries a reserved element variable
(`PROTOCOL_ELEM_VAR`) in every element-parametric target position, and applying
`Enumerable.t(integer)` instantiates it — so `list(...)` targets refine to
`list(integer)`. A bare `Enumerable.t` or a free-variable element
(`Enumerable.t(a)`) carries no refinement and resolves to the bare union of the
protocol's implementation target shapes.

## Callback Surface vs Domain Type

The protocol callback surface and the protocol-domain type are related but not
identical.

The callback surface is checked at implementation time. An implementation must
define every required callback with the required arity, and must not provide
callbacks the protocol never declared (`validate_protocol_impls`). Callback
spec compatibility is enforced: an implementation callback whose declared `spec`
contradicts the protocol's declared callback spec is rejected.

The domain type is checked at use sites and function boundaries. A spec that
requires `P.t(...)` requires proof that the argument type is inside the
implementation domain of `P`. That proof may come from a concrete impl target,
a closed union whose arms all implement `P`, or an explicitly open boundary.
Executable dispatch is emitted when the planner statically selects a single
implementation and, for any receiver overlapping two or more implementing
targets, as a `TypeTest`/`If` cascade (with a stub fallthrough when the receiver
is open or erased).

Because the protocol-domain type is a real union (not `any`), a use site that
passes an `Integer` where `Enumerable.t(a)` is required is rejected at spec
checking: `Integer` is disjoint from the `Enumerable` domain, so it fails the
generic "not a subtype of declared" check. A protocol call on a receiver wholly
outside the domain also raises a dedicated diagnostic at dispatch
(`type/protocol-no-impl`) naming the protocol, the receiver type, and the known
implementors.

## Implementation Targets

Implementation targets are typed identities. They are never display strings.

Implementation targets are module-shaped, keyed by typed module identity.
Built-in scalar and list names map to known type shapes when the planner checks
dispatch. Display spellings are diagnostics and source syntax; compiler facts use
a semantic `ImplTarget` identity, just as module linking uses `ModuleName` and
`ExportKey` instead of dotted strings.

Duplicate `(protocol, target)` implementations are errors. Missing required
callbacks and callback arity mismatches are errors. The diagnostics should name
the protocol, implementation target, callback, expected arity, actual arity,
and source spans when available.

## Open And Closed Domains

Library interfaces expose protocol declarations and implementation facts as
public contract data. Dependents can check protocol-domain specs from
interfaces without loading provider bodies.

Compilation can see two useful domain shapes:

- an open library domain, where future or unloaded modules may add
  implementations;
- a closed executable or link domain, where the linked implementation set is
  known.

Open domains type-check calls and specs. Executable dispatch is emitted when the
planner selects a single static implementation callback and, for any receiver
overlapping two or more implementing targets, as a `TypeTest`/`If` cascade of
per-target direct calls. An open or erased receiver's cascade ends in a stub
fallthrough for the unimplemented residual; a closed union resolves every value
to a direct implementation call. Because fz links whole programs, the linked
implementation set is known where the cascade is built — no separate
runtime-lookup table.

## Dispatch Outcomes

Protocol dispatch is a call-edge capability selected by the planner and linker.
It is not a separate string lookup path in codegen.

For a protocol call, the planner (`protocol_dispatch_key`) matches the receiver
type by subtype against the registered `(protocol, ImplTarget)` impls and selects
one of these outcomes:

- static direct (`ProtocolDispatch::Local`): a matching implementation lives in
  this unit, so the edge is an ordinary direct call to that implementation
  callback;
- provider-boundary external edge (`ProtocolDispatch::External`): the matching
  callback is known by `ExportKey`, but its body lives in another unit until
  module graph linking.

When no single target matches but the receiver overlaps two or more locally
implemented targets, a frontend rewrite
(`rewrite_closed_union_protocol_dispatch`, in `ir_planner::switch_dispatch`)
replaces the stub call with a `TypeTest`/`If` cascade of per-target direct
calls. Receiver narrowing makes each arm's call resolve to the right
implementation when the module is re-planned, so the cascade is ordinary
`TypeTest`/`If`/`Call` IR — it lowers in the interpreter, JIT, and AOT with no
dispatch-specific codegen. The rewrite lives in the shared frontend (beside
`apply_planned_direct_call_targets`), so the interpreter and codegen see the
same devirtualized IR.

The cascade covers both closed and open receivers. A closed union (the arms
cover the whole receiver, no residual) tests every arm but the last, which is
the final `else`. An open or erased receiver — an `any`, or a union with a
residual outside every implemented target — tests every arm and routes the
final `else` to a fallthrough that preserves the original stub call, so a
runtime value matching no implementation halts with `:protocol_dispatch_unplanned`
exactly as before the rewrite. No runtime lookup table is needed: fz links whole
programs (an unresolved import fails the link), so every implementation is known
at the point the cascade is built; the cascade is the dispatch table. Cascade
arms are local implementations; an overlapping target whose implementation is
external (a provider not yet linked) is left to the fallthrough, the same
boundary `protocol_dispatch_key` draws between local and external dispatch.

When the receiver is wholly outside the domain, the planner emits a dedicated
`type/protocol-no-impl` diagnostic at dispatch (naming the protocol, the
receiver type, and the known implementors); spec checking
(`spec_check::validate_specs`) also rejects a disjoint receiver via the ordinary
"not a subtype of declared" check.

Direct and switch dispatch do not require heap boxing of scalar receivers. The
selected callback ABI and the caller's argument shape cooperate the same way
direct-call variants and return-demand variants do; the cascade tests the
receiver's existing runtime tag (`Prim::TypeTest` distinguishes int, float,
atom, list, map, binary, and tuple-arity kinds in every engine).

## No-Replanning Rule

Planner facts are upstream facts. Link and load stages may validate, remap,
resolve, and strengthen those facts. They must not depend on a post-link
planner pass to reconstruct facts that were already known before linking.

Provider-backed execution should therefore preserve codegen-required planner
facts through the unit boundary:

- call-edge dispatch facts;
- return demand and return-context plans;
- function constant facts;
- extern marshal facts;
- protocol implementation edge facts.

`ExternalCallEdge` is the provider-boundary call edge. Protocol implementation
calls that cross a provider boundary use the same model: an implementation
callback is known by typed export identity before its local `FnId` is available.
Linking resolves that boundary edge and updates the preserved call-edge plan in
the same transformation that rewrites the IR.

Whole-program or LTO passes may add information that was not available
upstream. They must earn their place as strengthening passes, not cleanup
passes needed to make normal linking correct.

## Diagnostics

Protocol diagnostics are tied to the typed fact that failed. The resolver
(`validate_protocol_impls` plus the collection passes) and the planner's
dispatch pass (`collect_protocol_no_impl_diagnostics`) produce:

- duplicate implementation: names the `(protocol, target)` pair and points at
  both the first and the duplicate impl sites;
- duplicate protocol declaration, and duplicate callback declaration within a
  protocol;
- impl references an unknown protocol;
- missing callback: names the protocol, target, and the missing callback
  `name/arity`;
- callback arity mismatch: an impl that provides a declared callback name at the
  wrong arity is reported as an arity mismatch, distinct from "missing callback";
- callback spec mismatch: an impl callback whose declared spec contradicts the
  protocol's declared callback spec;
- unknown/extra callback: an impl that provides a callback the protocol never
  declared (at any arity), named by protocol, target, and `name/arity`;
- no implementation at dispatch (`type/protocol-no-impl`): a protocol call whose
  receiver type is disjoint from every implementing target, naming the protocol,
  receiver type, and known implementors.

A protocol-domain spec mismatch that names the failing parameter or return
position is not yet produced: such a constraint surfaces as the generic
spec-check "not a subtype" diagnostic.

These are compiler diagnostics, not runtime surprises, whenever the receiver
type is statically known enough to prove failure.

## Where This Lives

Protocol facts extend existing compiler ownership rather than a parallel
subsystem:

- `protocols::ProtocolRegistry` stores resolver-owned declarations and
  `(protocol, ImplTarget)` implementation facts.
- `resolve::flatten_modules` collects protocol facts while source-level
  protocol AST is still available, validates duplicate impls and callback
  coverage, and installs `Protocol.t` domain aliases in module type envs.
- `type_expr` parses dotted parametric protocol-domain spellings such as
  `Enumerable.t(integer)` and looks `Enumerable.t` up in the module type env. A
  concrete element argument instantiates the domain template's reserved element
  variable (refining `list(...)` targets); a bare `Enumerable.t` or free-variable
  element carries no refinement. The base domain is built by
  `resolve::protocol_domain_type` as an open nominal marker
  (`opaque_of(protocol_domain_tag)`) unioned with the known implementation
  target shapes, never `any`.
- `ModuleInterface` carries protocol declaration and implementation facts in
  interface fingerprints so artifacts can expose protocol contracts without
  provider bodies.
- `ModuleGraphLoader` traverses module imports, not protocol callback
  namespaces. A `defimpl` callback path is an export namespace inside the
  defining artifact; treating it as an artifact root creates false
  `Protocol/Target.fzi` dependencies.
- `ir_lower` records protocol callback calls as protocol stub callsites with
  stable `CallsiteId`s; `ir_planner` replaces those stubs with local or
  provider-boundary `CallEdgePlan` targets from receiver type facts.
- `link_ir_units` remaps protocol call facts and resolves provider
  protocol implementation callbacks to local call edges without a post-link
  planning pass. Link-time callsite rewrites must preserve the caller/identity
  match and target arity; arity mismatch means the candidate is not the same
  callsite.
- Frontend checking applies planned direct call targets back onto protocol
  stub callsites and rewrites closed-union receivers into `TypeTest`/`If`
  cascades (`ir_planner::switch_dispatch`) before interpretation or native
  emission. The interpreter and codegen therefore execute ordinary typed impl
  calls, preserving scalar argument representations such as raw integers.
- [`dispatch-as-planner-output.md`](dispatch-as-planner-output.md) defines planner-owned dispatch facts.
- `SpecPlan.call_edges` is keyed by `CallsiteId` and stores selected call-edge
  capabilities.
- `ReturnDemand` is already a call-edge capability selected before codegen.
- `ExternalCallEdge` represents known provider-boundary calls before link.
- `ModuleInterface` and `.fzi` artifacts carry public contract facts without
  provider bodies.
- `Types` owns type construction, queries, and decisions; protocol-domain
  types belong there.
