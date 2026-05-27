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

The v1 source forms are:

```fz
defprotocol Enumerable do
  @spec reduce(t(a), acc, fn(a, acc) -> acc) -> acc
  def reduce(enumerable, acc, reducer)
end

defimpl Enumerable, for: List do
  def reduce(list, acc, reducer) do
    ...
  end
end
```

`defprotocol` declares the protocol name, required callback names and arities,
public callback specs, and the protocol-domain type constructor
`Protocol.t(...)`.

`defimpl` declares the protocol it implements, the semantic implementation
target, and the callback bodies that satisfy the protocol.

`Protocol.t(...)` is not `any`. It is an implementation-domain constraint:
a value of type `Enumerable.t(a)` is a value for which an `Enumerable`
implementation is known, preserving the element parameter carried by the
protocol declaration.

## Callback Surface vs Domain Type

The protocol callback surface and the protocol-domain type are related but not
identical.

The callback surface is checked at implementation time. An implementation must
define every required callback with the required arity and compatible specs.

The domain type is checked at use sites and function boundaries. A spec that
requires `P.t(...)` requires proof that the argument type is inside the
implementation domain of `P`. That proof may come from a concrete impl target,
a closed union whose arms all implement `P`, or an explicitly open boundary
that remains a runtime lookup.

This lets the compiler produce diagnostics such as "List implements
Enumerable, Integer does not" instead of treating a protocol annotation as
plain `any`.

## Implementation Targets

Implementation targets are typed identities. They are never display strings.

The v1 target space is built-in targets, module or struct targets keyed by typed
module identity, and `Any` only if the protocol explicitly permits an `Any`
fallback. Display spellings are diagnostics and source syntax. Compiler facts
use a semantic `ImplTarget` identity, just as module linking uses `ModuleName`
and `ExportKey` instead of dotted strings.

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

Open domains can still type-check calls and specs, but dispatch may remain a
runtime lookup when the receiver type does not identify one implementation.
Closed domains allow the planner to choose direct calls or finite switches
without a fallback path.

## Dispatch Outcomes

Protocol dispatch is a call-edge capability selected by the planner and linker.
It is not a separate string lookup path in codegen.

For a protocol call, the compiler must select one of these outcomes:

- static direct: the receiver type has one known implementation, so the edge is
  an ordinary direct call to that implementation callback;
- closed-domain switch: the receiver type is a finite union of known
  implementation targets, so the edge is a matcher or switch whose arms call
  the selected implementation callbacks;
- provider-boundary external edge: the implementation callback is known by
  `ExportKey`, but its body lives in another unit until module graph linking;
- runtime lookup: the receiver domain is genuinely open or erased;
- diagnostic: no implementation can satisfy the protocol-domain constraint.

Static direct and closed-domain switch dispatch must not require heap boxing of
scalar receivers. The selected callback ABI and the caller's argument shape
cooperate the same way direct call variants and return-demand variants do
today.

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
- protocol implementation edge facts once protocols exist.

`ExternalCallEdge` is the existing provider-boundary call edge. Protocol
implementation calls that cross a provider boundary should use the same model:
an implementation callback is known by typed export identity before its local
`FnId` is available. Linking resolves that boundary edge and updates the
preserved call-edge plan in the same transformation that rewrites the IR.

Whole-program or LTO passes may add information that was not available
upstream. They must earn their place as strengthening passes, not cleanup
passes needed to make normal linking correct.

## Diagnostics

Protocol diagnostics should be tied to the typed fact that failed:

- missing implementation: name the protocol, required domain type, actual
  receiver type, and known implementors in scope;
- duplicate implementation: name the `(protocol, target)` pair and both
  implementation sites;
- callback arity mismatch: name the protocol callback and expected/actual
  arity;
- callback spec mismatch: name the callback and show the required protocol
  spec against the implementation spec;
- protocol-domain spec mismatch: name the parameter or return position whose
  `Protocol.t(...)` constraint failed.

These are compiler diagnostics, not runtime surprises, whenever the receiver
type is statically known enough to prove failure.

## Current Anchors

The implementation should extend existing compiler ownership instead of
creating a parallel subsystem:

- `docs/dispatch-as-planner-output.md` defines planner-owned dispatch facts.
- `SpecPlan.dispatches` is keyed by `CallsiteId` and currently stores direct
  target `SpecKey` values.
- `ReturnDemand` is already a call-edge capability selected before codegen.
- `ExternalCallEdge` represents known provider-boundary calls before link.
- `ModuleInterface` and `.fzi` artifacts carry public contract facts without
  provider bodies.
- `Types` owns type construction, queries, and decisions; protocol-domain
  types belong there.
