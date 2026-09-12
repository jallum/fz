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
  def reduce(enumerable, acc, reducer)
end

defimpl Enumerable, for: List do
  def reduce(list, acc, reducer), do: List.reduce(list, acc, reducer)
end
```

The `def` in a protocol body is still lexed as an identifier. The protocol
body reader accepts that identifier in its callback slot and the ordinary
quoted-surface extractor derives the callback name and arity. `defp` is not a
protocol callback form; callback declarations also require at least one
parameter and accept neither a body nor a guard. Implementation bodies use the
same grouped `def` surface and `FunctionSource` publication path as module
functions.

`defprotocol Enumerable` publishes a first-class namespace at its lexical path
(a root declaration publishes `Enumerable`, not `Enumerable.Enumerable`). It owns
the required callback names/arities and their public specs. `defimpl` declares
the protocol, the target, and the callback bodies; the callbacks lower into a
**protocol-owned** module identified by `ModuleDenotation::ProtocolImpl { protocol,
target }` in the ordinary `ModuleMap`. `defimpl Enumerable, for: List` displays
`Enumerable.List.reduce/3`, so the body can delegate to ordinary target helpers
like `List.reduce/3` without colliding. The protocol/target boundary is retained:
`(A, B.C)`, `(A.B, C)`, and the named module `A.B.C` are three distinct owners
even though all display `A.B.C`. Function denotations and their AOT carrier keep
this same typed module identity; no callback or closure comparison uses the
display projection.

Projected `__CALLER__.module` aliases retain this portable denotation in quoted
metadata. A macro that emits `unquote(__CALLER__.module).val(x)` therefore calls
the implementation's own callback, even when an ordinary named module shares
its display path. Both source projection and quote reification consume the one
`ModuleDenotation::quoted_parts` encoding shape.

The runtime library follows Elixir's split: `Enumerable` is the protocol; `Enum`
is the convenience module users call. Low-level control tuples
(`{:cont|:halt|:suspend, acc}`) stay on `Enumerable.reduce/3`; `Enum.reduce/2,3`
returns plain accumulator values.

## The owned facts

`World` carries these protocol facts:

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
  `protocol -> [(target, impl_module)]`. `register_protocol_impl` records an
  entry per `defimpl` while scoping (no body defined yet). It is the *only* way
  dispatch finds an unloaded impl: a receiver with no arm demands
  `DefineModule(impl_module)` for each overlapping target. A `defimpl` is
  thus independently demandable — its lexical host is never the unit of demand.

`protocol_callback(fn)` answers "is this function a protocol callback?". It reads
the registry, and `derived_protocol_callback` covers two cases the registry does
not hold explicitly: a runtime-library module whose interface declares the
callback, and a function in a module indexed as `ModuleSourceKind::Protocol`.
That is how runtime protocols such as `Enumerable` are recognized without a
user `defprotocol` in the program.

## Implementation targets

An `ImplTarget` is a module identity, never a display string. Builtin targets
are exact top-level source names and map to their concrete value family:

```text
List -> list(any)   Integer -> int   Float -> float   Atom -> atom
Binary -> str       Map -> map_top
```

A qualified name such as `X.List` is a nominal target unless its own
`StructDefined` fact supplies a struct; sharing a final segment with a builtin
does not classify it as that builtin.

A named source struct (e.g. `Range`) maps to one tagged record carrying its
parsed `ModuleName` and declared fields together. The tag keeps it disjoint
from a plain map with identical fields; its `ModuleId` records the World
dependency, while the typed source name owns equality and ordering. A target
with no `StructDefined` fact remains `OpaqueTag::ProtocolTarget(ModuleName)`
in the existing opaque set algebra. Ordinary named opaque spellings cannot
manufacture protocol targets. Runtime predicates project the typed target
name directly, without recognizing a string prefix.

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
no match           -> demand the typed impl owner (from the provider
                      index) whose target overlaps the receiver, then retry
many matches       -> unresolved (any): the receiver is open/ambiguous here
```

The runtime-predicate check is what keeps runtime identity authoritative. A
named struct is a tagged record, not a plain map; the `Enumerable` impl for `Range` therefore
does not overlap the `Map` impl just because the two record shapes have fields.

Selection is lazy about impl code, and there is a single discovery path: the
**provider index** (`ProtocolImplProviders(protocol)`). Scope time records every
`defimpl` as a `(protocol, target) -> impl_module` entry — built-in impls
co-located with the protocol's own source, and impls in a module the program
never reaches by name alike. When no registered arm matches, the job reads that
index and demands `DefineModule(impl_module)` for each target the receiver
overlaps by the same runtime-predicate-plus-intersection test; the impl is the
unit of demand, not the arbitrarily-named module it
sits inside, and its lexical host is never pulled. There is **no** receiver-type
module-name scan: a protocol call always names the protocol, and that reference
scopes its co-located `defimpl`s, so built-in impls ride in on the protocol. A
single match activates `selected.function` through the ordinary call path — so a
known list receiver at `Enumerable.reduce/3` resolves to the List impl callback
(displayed `Enumerable.List.reduce/3`), and the callsite summary identifies that
concrete callee, no stub and no runtime
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

Function contracts classify protocol-domain obligations from this resolved
marker, after aliases and bounds have become hard `Ty` values. The durable key is
the marker tag (`protocol::<Name>.t`) wrapped as `ProtocolDomainObligation`.
`collect_spec_refs` remains a source-publication dependency/wait tool; contract
enforcement must not rewalk source refs or enumerate protocol implementations.

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
                     ModuleSourceKind::ProtocolImpl source owned by the typed pair
                     (World::reference_protocol_impl_module) and records it in the
                     provider index; publish_protocol_impl_surface (define tier,
                     run by DefineModule(impl_module)) lowers the callbacks
                     and revises the dispatch fact
compiler2/protocol.rs  the ProtocolCallback / ProtocolImpl fact shapes + maps
world.rs             define/read protocol facts; impl_target_ty;
                     protocol_impl_providers (the discovery surface);
                     protocol-domain tags for normal TypeDefined derivation
jobs/semantic.rs     resolve_protocol_call — the receiver-subtype selection above
```

## Proof gates

```text
cargo test --lib compiler2::semantic_analysis_test::compiler2_protocol_impl_resolves_to_owned_module_not_host
cargo test --lib compiler2::semantic_analysis_test::compiler2_root_colocated_protocol_impl_registers_on_scope
cargo test --lib compiler2::drive_test::compiler2_protocol_domain_marker_stays_type_owned_while_dispatch_revises_when_impls_land
```
