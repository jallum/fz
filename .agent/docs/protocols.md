# Protocols

A protocol is a typed compiler fact, not a generated dispatch module. It bundles
two things:

- a **callback surface** — the function names and arities an implementation must
  provide;
- a **domain type marker** — `Protocol.t(...)`, the protocol-owned opaque type
  name specs can refer to without depending on the current impl set.

fz keeps Elixir's source shape (`defprotocol` / `defimpl`, plus a convenience
module like `Enum`), but the semantic object is a registry fact. The pieces:

- `ProtocolCallback` / `ProtocolImpl` (`src/compiler2/protocol.rs`) — the owned
  facts: which protocol a callback belongs to, and a protocol's per-target impl.
- `ImplTarget` — the module a `defimpl` is *for*, mapped to a concrete type when
  dispatch is checked.
- `resolve_protocol_call` (`jobs/semantic.rs`) — selects the impl at a callsite
  from receiver type facts.

## Source contract

```fz
defprotocol Enumerable do
  @spec reduce(t(a), b, (a, b) -> {:cont, b} | {:halt, b}) :: any
  fn reduce(enumerable, acc, reducer)
end

defimpl Enumerable, for: List do
  fn reduce(list, acc, reducer), do: List.reduce(list, acc, reducer)
end
```

`defprotocol Enumerable` publishes a first-class namespace at its lexical path
(a root declaration publishes `Enumerable`, not `Enumerable.Enumerable`). It owns
the required callback names/arities and their public specs. `defimpl` declares
the protocol, the target, and the callback bodies; the callbacks lower into a
**protocol-owned** module named `protocol.child(target)` — `defimpl Enumerable,
for: List` produces `Enumerable.List.reduce/3` (`reference_protocol_impl_module`),
not a function on `List`, so the body can delegate to ordinary target helpers
like `List.reduce/3` without colliding.

The runtime library follows Elixir's split: `Enumerable` is the protocol; `Enum`
is the convenience module users call. Low-level control tuples
(`{:cont|:halt|:suspend, acc}`) stay on `Enumerable.reduce/3`; `Enum.reduce/2,3`
returns plain accumulator values.

## The owned facts

`World` carries two registries:

- **`ProtocolCallbackMap`** — `function -> ProtocolCallback { protocol }`.
  `define_protocol_callback` fills it while indexing a `defprotocol` surface, so
  a callback function knows the protocol it answers to.
- **`ProtocolImplMap`** — `ProtocolImplKey { protocol, target } -> ProtocolImpl`,
  where a `ProtocolImpl` maps each `(name, arity)` to a
  `ProtocolCallbackImpl { function, owner_module }`. `define_protocol_impl` fills
  it while indexing a `defimpl`.
- **`ProtocolDispatchMap`** — `protocol -> ProtocolDispatch { arms }`, derived
  from the impl registry. Protocol definition publishes the empty dispatch fact;
  each `defimpl` revises this dispatch fact and only this dispatch fact.
- **`ProtocolImplProviders`** — the scope-tier discovery surface:
  `protocol -> [(target, Protocol.Target)]`. `register_protocol_impl` records an
  entry per `defimpl` while scoping (no body defined yet). It is the *only* way
  dispatch finds an unloaded impl: a receiver with no arm demands
  `DefineModule(Protocol.Target)` for each overlapping target. A `defimpl` is
  thus independently demandable — its lexical host is never the unit of demand.

`protocol_callback(fn)` answers "is this function a protocol callback?". It reads
the registry, and `derived_protocol_callback` covers two cases the registry does
not hold explicitly: a runtime-library module whose interface declares the
callback, and a function in a module indexed as `ModuleSourceKind::Protocol`.
That is how runtime protocols such as `Enumerable` are recognized without a
user `defprotocol` in the program.

## Implementation targets

An `ImplTarget` is a module identity, never a display string. `impl_target_ty`
maps a target's last segment to a concrete type:

```text
List -> list(any)   Integer -> int   Float -> float   Atom -> atom
Binary -> str       Map -> map_top    <other> -> struct_impl_target_type(name)
```

A named source struct (e.g. `Range`) maps to its nominal opaque tag
`opaque(impl-target::Range)` (see [`set-theoretic-types`](set-theoretic-types.md)),
which keeps it distinct from any structurally-similar value.

## Dispatch is receiver/target overlap selection

A protocol callsite is an ordinary call whose callee is a protocol callback
function. When `resolve_function_call` sees `protocol_callback(fn)`, it hands off
to `resolve_protocol_call`, which selects an implementation from the receiver
type — the first argument:

```text
receiver = input_types[0]
for each registered (protocol, target) impl:
    if runtime_type_predicate(receiver) overlaps runtime_type_predicate(impl_target_ty(target))
       and intersect(receiver, impl_target_ty(target)) is non-empty
       and it has this callback:
        collect it
exactly one match  -> activate that impl callback as an ordinary call
                      (the protocol callsite becomes a direct call to the impl)
no match           -> demand the impl module Protocol.Target (from the provider
                      index) whose target overlaps the receiver, then retry
many matches       -> unresolved (any): the receiver is open/ambiguous here
```

The runtime-predicate check is what keeps runtime identity authoritative. A
named struct value can carry structural field evidence, including map-shaped
evidence, but it is not a plain runtime map; `Enumerable.Range` therefore does
not overlap the `Map` impl just because the `Range` struct has fields.

Selection is lazy about impl code, and there is a single discovery path: the
**provider index** (`ProtocolImplProviders(protocol)`). Scope time records every
`defimpl` as a `(protocol, target) -> Protocol.Target` entry — built-in impls
co-located with the protocol's own source, and impls in a module the program
never reaches by name alike. When no registered arm matches, the job reads that
index and demands `DefineModule(Protocol.Target)` for each target the receiver
overlaps by the same runtime-predicate-plus-intersection test; the impl is the
unit of demand, not the arbitrarily-named module it
sits inside, and its lexical host is never pulled. There is **no** receiver-type
module-name scan: a protocol call always names the protocol, and that reference
scopes its co-located `defimpl`s, so built-in impls ride in on the protocol. A
single match activates `selected.function` through the ordinary call path — so a
known list receiver at `Enumerable.reduce/3` resolves to `Enumerable.List.reduce/3`
and the callsite summary names that concrete callee, no stub and no runtime
lookup table.

## The domain type

`Protocol.t(...)` is a declaration-owned opaque marker:
`opaque(protocol_domain_tag(protocol))`. Protocol publication notes `t/0` and
`t/1` as normal type declarations; `DeriveTypeDef` resolves them only when a
consumer demands their `TypeDefined` fact. `t/1` keeps its formal parameter, but
the resolved hard type is the same interned marker as `t/0`; the impl set never
widens or revises the type fact.

This keeps the type layer separate from the dispatch layer. A protocol marker is
not a dispatch matrix and is not the union of known implementations. Runtime
dispatch still matches the receiver against implementation-target types directly
inside `resolve_protocol_call`.

## Callback surface vs domain

The two are checked in different places. The **callback surface** is validated at
implementation time: an impl must define every required callback at the required
arity and none the protocol never declared, and when both protocol and impl carry
`@spec`s their arrows are compared per position, rejecting only on proved
set-theoretic disjointness (so free variables and `any` never false-positive).
The **domain type** is a normal `TypeDefined` dependency: consumers that mention
`P.t(...)` demand `DeriveTypeDef(P.t)` and read the protocol-owned marker. It is
not revised by `defimpl`.

## Where the facts live

```text
jobs/source.rs       indexes defprotocol (define_protocol_surface ->
                     define_protocol_callback)
source_publish.rs    register_protocol_impl (scope tier) hoists each defimpl to a
                     ModuleSourceKind::ProtocolImpl source named Protocol.Target
                     (reference_protocol_impl_module) and records it in the
                     provider index; publish_protocol_impl_surface (define tier,
                     run by DefineModule(Protocol.Target)) lowers the callbacks
                     and revises the dispatch fact
compiler2/protocol.rs  the ProtocolCallback / ProtocolImpl fact shapes + maps
world.rs             define/read protocol facts; impl_target_ty;
                     protocol_impl_providers (the discovery surface);
                     protocol-domain tags for normal TypeDefined derivation
jobs/semantic.rs     resolve_protocol_call — the receiver-subtype selection above
```

## Proof gates

```text
cargo test --lib compiler2::semantic_analysis_test::compiler2_protocol_impl_resolves_to_concat_module_not_host
cargo test --lib compiler2::semantic_analysis_test::compiler2_root_colocated_protocol_impl_registers_on_scope
cargo test --lib compiler2::drive_test::compiler2_protocol_domain_marker_stays_type_owned_while_dispatch_revises_when_impls_land
```
