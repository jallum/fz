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
implementation is known. The element parameter spelled in `Enumerable.t(a)` is
parsed but currently discarded — the resolved domain is the bare union of the
protocol's known implementation target shapes, with no element refinement.

## Callback Surface vs Domain Type

The protocol callback surface and the protocol-domain type are related but not
identical.

The callback surface is checked at implementation time. An implementation must
define every required callback with the required arity, and must not provide
callbacks the protocol never declared (`validate_protocol_impls`). Callback
spec compatibility is not yet enforced: the declared callback `spec` is stored
on `ProtocolCallbackFact` but currently carries `#[allow(dead_code)]` pending a
later protocol ticket.

The domain type is checked at use sites and function boundaries. A spec that
requires `P.t(...)` requires proof that the argument type is inside the
implementation domain of `P`. That proof may come from a concrete impl target,
a closed union whose arms all implement `P`, or an explicitly open boundary.
Executable dispatch is emitted only when the planner statically selects a single
implementation; open-boundary runtime lookup is not emitted.

Because the protocol-domain type is a real union (not `any`), a use site that
passes an `Integer` where `Enumerable.t(a)` is required is rejected at spec
checking: `Integer` is disjoint from the `Enumerable` domain, so it fails the
generic "not a subtype of declared" check. A protocol-specific message such as
"List implements Enumerable, Integer does not" is not yet produced.

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

Open domains type-check calls and specs. Executable dispatch is emitted only
when the planner selects a single static implementation callback; open or erased
receiver domains get no runtime-lookup fallback. Closed domains let the planner
choose a direct call to the selected implementation without a fallback path.

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

When no impl matches, `protocol_dispatch_key` returns `None`: the planner does
not yet emit a dedicated "no implementation" diagnostic. The unplanned protocol
stub is left in place, and rejection happens earlier at spec checking
(`spec_check::validate_specs`), where a receiver type disjoint from the
protocol-domain union fails the ordinary "not a subtype of declared" check.

Finite-union switch dispatch and runtime lookup for open or erased receiver
domains are not emitted.

Static direct dispatch does not require heap boxing of scalar receivers. The
selected callback ABI and the caller's argument shape cooperate the same way
direct-call variants and return-demand variants do.

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
(`validate_protocol_impls` plus the collection passes) currently produces:

- duplicate implementation: names the `(protocol, target)` pair, carrying the
  span of the duplicate impl site (a single span, not both sites);
- duplicate protocol declaration, and duplicate callback declaration within a
  protocol;
- impl references an unknown protocol;
- missing callback: names the protocol, target, and the missing callback
  `name/arity` (an arity that does not match a declared callback surfaces here
  rather than as a distinct "arity mismatch" message);
- unknown/extra callback: an impl that provides a callback the protocol never
  declared, named by protocol, target, and `name/arity`.

The following diagnostics are intended but not yet implemented: a use-site
"missing implementation" message naming the receiver type and known
implementors; a dedicated callback-arity-mismatch message; a callback spec
mismatch; and a protocol-domain spec mismatch naming the failing parameter or
return position. A protocol-domain constraint that fails today surfaces only as
the generic spec-check "not a subtype" diagnostic.

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
  `Enumerable.t(integer)` (the type arguments are consumed and discarded) and
  looks `Enumerable.t` up in the module type env. The looked-up type is built by
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
  stub callsites before interpretation or native emission. The interpreter and
  codegen therefore execute ordinary typed impl calls, preserving scalar
  argument representations such as raw integers.
- [`dispatch-as-planner-output.md`](dispatch-as-planner-output.md) defines planner-owned dispatch facts.
- `SpecPlan.call_edges` is keyed by `CallsiteId` and stores selected call-edge
  capabilities.
- `ReturnDemand` is already a call-edge capability selected before codegen.
- `ExternalCallEdge` represents known provider-boundary calls before link.
- `ModuleInterface` and `.fzi` artifacts carry public contract facts without
  provider bodies.
- `Types` owns type construction, queries, and decisions; protocol-domain
  types belong there.
