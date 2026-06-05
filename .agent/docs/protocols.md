# Protocols

A protocol is a typed compiler fact, not a generated dispatch module. It bundles
two things:

- a **callback surface** — the function names and arities an implementation must
  provide;
- a **domain type** — `Protocol.t(...)`, the set of values that are known to have
  an implementation.

fz keeps Elixir's source shape (`defprotocol`/`defimpl`/a convenience module like
`Enum`) but the semantic object is a registry fact that participates in planning,
linking, diagnostics, and representation choices. The pieces to hold in your head:

- `ProtocolRegistry` (in `frontend/protocols.rs`) — the resolver-owned store of
  protocol declarations and `(protocol, target)` implementation facts.
- `ImplTarget` — the typed identity of what an impl is *for* (a `ModuleName`,
  mapped to a concrete type shape when dispatch is checked).
- the **domain type** — an opaque domain tag unioned with each implementing
  target's type, built by `resolve::protocol_domain_template`.
- the **protocol stub** — a `__protocol__.<callback>` fn the lowerer emits at each
  protocol callsite; the planner rewrites the call edge to a real impl.
- `protocol_dispatch_key` (in `ir_planner/walk.rs`) — the planner step that turns a
  stub call into a local or provider-boundary call edge.

## Source Contract

```fz
defprotocol Enumerable do
  @spec reduce(t(a), b, (a, b) -> {:cont, b} | {:halt, b}) :: any
  fn reduce(enumerable, acc, reducer)
end

defimpl Enumerable, for: List do
  fn reduce(list, acc, reducer), do: List.reduce(list, acc, reducer)
end

defmodule Enum do
  @spec reduce(Enumerable.t(a), b, (a, b) -> b) :: b
  fn reduce(enumerable, acc, reducer), do: ...
end
```

`defprotocol Enumerable` publishes a first-class protocol namespace at its lexical
module path: a root declaration publishes `Enumerable`; the same declaration inside
`defmodule Foo` publishes `Foo.Enumerable` (`resolve::qualify_protocol_name`). That
namespace owns the required callback names and arities, the public callback specs,
and the protocol-domain constructor `Protocol.t(...)`.

A protocol namespace is not a wrapper module: a root `defprotocol Enumerable`
publishes `Enumerable`, not `Enumerable.Enumerable`. The module-contract layer
represents the protocol with a module-shaped `ModuleInterface` because imports,
module contracts, linking, and qualified references already speak in public namespace
identities. The source semantic object stays the protocol fact.

`defimpl` declares the protocol it implements, the target, and the callback bodies.
Callbacks lower into implementation modules owned by the protocol — `defimpl
Enumerable, for: List` produces `Enumerable.List.reduce/3`
(`resolve::protocol_impl_module` = `protocol.child(target_last_segment)`), not into
the target module. The body can delegate to ordinary target helpers like
`List.reduce/3` without colliding with them.

The runtime library follows Elixir's public naming split: `Enumerable` is the
protocol identity and domain type, while `Enum` is the convenience module users
call. `Enum.sort/1` and `Enum.sort/2` are ordinary runtime-library FZ functions backed by
a stable merge sort over lists (the private `sort_list`/`merge_sort_lists` helpers,
which keep the left element on a tie). Low-level protocol-control tuples stay on
`Enumerable.reduce/3`; the public `Enum.reduce/2,3` returns plain accumulator values
(its `reduce_finish` unwraps `{:done, acc}` / `{:halted, acc}` / `{:suspended, acc,
_}`).

## Callback Surface vs Domain Type

The callback surface and the domain type are related but checked in different
places.

The **callback surface** is checked at implementation time
(`resolve::validate_protocol_impls`). An implementation must define every required
callback at the required arity and must not provide a callback the protocol never
declared. Callback specs are ordered overload sets. When both the protocol callback
and the impl callback carry `@spec`s, `validate_protocol_callback_specs` binds the
domain variable `t` to the impl's concrete target type, then compares each impl
arrow against the protocol arrow set per position. A position rejects only on proved
set-theoretic disjointness (empty intersection), so free type variables and `any`
never create a false positive.

The **domain type** is checked at use sites and function boundaries. A spec that
requires `P.t(...)` requires proof that the argument type is inside `P`'s domain,
which may come from a concrete impl target, a closed union whose arms all implement
`P`, or an explicitly open boundary.

Because the domain is a real union (not `any`), passing an `Integer` where
`Enumerable.t(a)` is required fails the generic `spec_check::validate_specs` "not a
subtype of any declared @spec arrow" check (`Integer` is disjoint from the
`Enumerable` domain). The planner adds a protocol-specific message on top (see
Dispatch Outcomes).

`Protocol.t(...)` is not `any`. It is the union of `opaque_of(protocol_domain_tag)`
with every known implementation target's type. The element parameter spelled in
`Enumerable.t(a)` is a real refinement, not discarded: `type_expr` instantiates the
domain template's `PROTOCOL_ELEM_VAR` with the argument, so a concrete element
refines element-parametric targets (`List` from `list(any)` to `list(elem)`). An
element that still mentions a free type variable carries no refinement, so it falls
back to `any` (the bare domain) and dispatch is left unperturbed. Scalar and map
targets are not parametric in a single element, so the element does not refine them.

## Implementation Targets

Implementation targets are typed identities, never display strings. The only
variant is `ImplTarget::Module(ModuleName)`. `impl_target_type_with_element` maps a
target's last segment to a concrete type shape: `List` → `list(element)`, `Integer`
→ `int`, `Float` → `float`, `Atom` → `atom`, `Binary` → `str`, `Map` → `map_top`,
and any other name → `opaque_of("impl-target::<name>")` (a named source struct such
as `Range`). Display spellings (`ImplTarget::display_name`) are for diagnostics and
source syntax; compiler facts use the `ImplTarget` identity, just as linking uses
`ModuleName` and `ExportKey` instead of dotted strings.

## Open And Closed Domains

Library interfaces expose protocol declarations and implementation facts as public
contract data, so dependents can check protocol-domain specs from compiler-owned
module contracts without loading provider bodies. Compilation sees two domain shapes:

- an **open** library domain, where unloaded modules may add implementations;
- a **closed** executable/link domain, where the linked implementation set is known.

Open domains type-check calls and specs. Executable dispatch is emitted only when
the planner selects a single static implementation callback; open or erased receiver
domains get no runtime-lookup fallback. Closed domains let the planner pick a direct
call to the selected implementation with no fallback path.

Within one unit the direct-call rewrite runs to a fixed point
(`frontend::apply_planner_rewrites_to_fixed_point`): applying one protocol edge can
make a later continuation reachable, revealing more protocol calls, so the loop
re-plans and re-applies until nothing changes.

## Dispatch Outcomes

Protocol dispatch is a call-edge capability the planner and linker select, recorded
as an ordinary `CallEdgePlan`. It is not a separate string-lookup path in codegen.

For a protocol callsite, `protocol_dispatch_key` reads the receiver (first argument)
type, matches it by subtype against the registered `(protocol, ImplTarget)` impls,
and returns one of:

- `ProtocolDispatch::Local(SpecKey, n_params)` — a matching impl lives in this unit;
  the edge becomes an ordinary direct call (`CallEdgeTarget::Local`) to that impl
  callback.
- `ProtocolDispatch::External { target: ExportKey, input, demand }` — the matching
  callback is known by `ExportKey` but its body lives in another unit until module
  linking; recorded as `CallEdgeTarget::External`.

When no impl matches, `protocol_dispatch_key` returns `None` and the unplanned
`__protocol__` stub is left in place. Two checks catch the failure with a clear
message:

- `spec_check::validate_specs` rejects a receiver disjoint from the domain union via
  the generic "not a subtype" check;
- `ir_planner::diagnostics::collect_protocol_no_impl_diagnostics` emits
  `type/protocol-no-impl` (`codes::TYPE_PROTOCOL_NO_IMPL`) at any protocol callsite
  whose receiver type is disjoint from the protocol's domain. The message names the
  protocol and the rendered receiver type, notes that the callback dispatches on its
  first argument, and lists the known implementors (or notes the protocol has none).
  The disjointness trigger is sound: `any`, a free variable, or the domain type
  itself overlaps the domain and never fires.

A finite-union receiver — `integer | list(...)` where both `Integer` and `List`
implement the protocol — has no single subtype match, so `protocol_dispatch_key`
leaves the stub. `rewrite_closed_union_protocol_dispatch` then rewrites that callsite
into a `TypeTest`/`If` cascade with one direct-call arm per *local* implementing
target the receiver overlaps:

```text
  t0 = TypeTest(recv, integer)
  if t0 -> arm_int  else -> arm_list
arm_int:    Enumerable.Integer.cb(recv, …) -> K
arm_list:   Enumerable.List.cb(recv, …)    -> K
```

`narrow::narrow_for_cond` intersects `recv` with the arm's target in the `then` arm
and differences it in the `else` arm, so when `plan_module` re-types the rewritten
module each arm's receiver is its target type and the ordinary direct-call planner
specs it to the right impl. The same path handles named source structs such as
`Range` by testing their struct schema id, alongside kind tests for lists and maps.

A receiver fully covered by its arms (a closed union) tests every arm but the last,
which is the final `else`. An open or erased receiver tests every arm and routes the
final `else` to a fallthrough block that preserves the original stub call, so a
runtime value matching no arm halts with `protocol_dispatch_unplanned` — the same
behavior as an unplanned stub. An overlapping target whose impl is external (a
provider outside this unit) makes the receiver not fully covered: its overlap becomes
residual handled by the fallthrough, the same local/external boundary
`protocol_dispatch_key` draws. `TypeTest`, `If`, and `Call` already lower in the
interpreter, JIT, and AOT, so the rewrite holds three-path parity with no new
codegen.

Static direct dispatch does not require heap boxing of scalar receivers. The
selected callback ABI and the caller's argument shape cooperate the same way
direct-call variants and planner-authored return contracts do, so a `List` receiver
stays a list and an integer receiver stays a raw integer.

## Why Linking Does Not Re-Plan

Planner facts are upstream facts. The link and load stages validate, remap, resolve,
and strengthen them; they do not run a fresh planner pass to reconstruct facts that
were already known before linking. Provider-backed execution therefore preserves the
codegen-required planner facts across the unit boundary: call-edge dispatch facts,
return contracts, function constant facts, extern marshal facts, and protocol
implementation edge facts.

`ExternalCallEdge` (a `CallsiteId` plus an `ExportKey` target) is the
provider-boundary call edge. A protocol callback that crosses a provider boundary
uses the same model: the impl callback is known by typed export identity before its
local `FnId` exists. `IrUnitLinker::resolve_external_call_edges_in_plan` rewrites
each boundary callsite to its resolved local `FnId` *and* flips the preserved
`CallEdgeTarget::External` to `CallEdgeTarget::Local` in the same transformation, so
the linked module's call-edge plan needs no replan to be correct. The compile
pipeline then runs one authoritative `plan_module` over the merged module before
codegen; whole-program/LTO passes only *strengthen* facts and never substitute for
ordinary linking.

## Where Protocol Facts Live

Protocol facts extend existing compiler ownership rather than a parallel subsystem.

- `frontend/protocols.rs` owns `ProtocolRegistry` — `protocols:
  BTreeMap<ModuleName, ProtocolDecl>` and `impls: BTreeMap<ProtocolImplKey,
  ProtocolImplFact>`. A `ProtocolImplFact` carries the protocol, the `ImplTarget`,
  the callbacks keyed by `(name, arity)` → `ExportKey`, and each impl callback's
  declared `@spec`s (`callback_specs`, empty for interface-sourced impls).
- `resolve::flatten_modules` collects protocol facts while source-level protocol AST
  is available: it validates duplicate impls and callback coverage
  (`validate_protocol_impls`), checks callback-spec compatibility
  (`validate_protocol_callback_specs`), and installs `Protocol.t` domain aliases
  (the element-refining template) in module type envs.
- `type_expr` parses dotted parametric domain spellings such as
  `Enumerable.t(integer)`, looks `Enumerable.t` up as a `ProtocolDomain` alias, and
  instantiates its `PROTOCOL_ELEM_VAR` with the (concrete) element.
- `ModuleInterface` carries `protocols` and `protocol_impls` in interface
  fingerprints so compiler-owned module contracts expose protocol facts without
  provider bodies. A top-level `defprotocol` contributes its own interface keyed by the
  protocol namespace; a nested protocol contributes its facts to the containing
  module interface under its fully qualified name. Callback specs travel as ordered
  overload sets (`InterfaceProtocolCallback.specs`), preserving input/result
  correlation through contract collection and compatibility checking.
- the compiler traverses module imports and runtime reachability from source,
  not protocol callback namespaces. A `defimpl` callback path such as
  `Enumerable.List.reduce/3` is an export namespace inside the defining source module;
  treating it as a module root would create false `Protocol/Target`
  dependencies. A nested protocol declared in the same module interface is already
  loaded, so a `defimpl Contracts.Collectable` inside `Contracts` does not make the
  loader request a separate `Contracts.Collectable` source root.
- `ir_lower` records each protocol callback call as a call to a `__protocol__.<name>`
  stub fn that halts with the atom `protocol_dispatch_unplanned`, keyed in
  `Module.protocol_call_targets: HashMap<FnId, ProtocolCallTarget>`. Prelude protocol
  facts are carried into the lowered module so runtime-library implementations of
  `Enumerable` for `List`, `Range`, and `Map` are visible to planner dispatch.
- `ir_planner` replaces those stub call edges with local or provider-boundary
  `CallEdgePlan`s from receiver type facts (`protocol_dispatch_key`), and
  `SpecPlan.call_edges` (keyed by `CallsiteId`) stores the selected call-edge
  capability and return contract.
- `link_ir_units` copies and remaps protocol facts (`copy_protocol_facts` carries
  `protocol_call_targets` and the registry; `copy_exports` registers impl callbacks
  in the export map) and resolves provider impl callbacks to local call edges with no
  post-link planning pass. A link-time callsite rewrite must match the
  caller/identity and target arity; an arity mismatch means a different callsite.
  Linked modules also carry `defstruct` schemas and intern struct field names so
  provider-backed struct patterns share the same schema/atom facts as same-unit code.

`ReturnDemand` is part of planner entry keys and call-edge contracts, but semantic
returns and executable bodies are keyed by `BodyKey`. `Types` owns type
construction, queries, and decisions; protocol-domain types are built there. Planner
dispatch facts are detailed in [`dispatch-as-planner-output.md`].

[`dispatch-as-planner-output.md`]: dispatch-as-planner-output.md
