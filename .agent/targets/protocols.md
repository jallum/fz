# Protocols

A protocol is a typed compiler fact, not a generated dispatch module. It bundles two
things:

- a **callback surface** — the function names and arities an implementation must
  provide;
- a **domain marker** — `Protocol.t(...)`, the nominal type that names "a value with
  an implementation."

fz keeps Elixir's source shape (`defprotocol` / `defimpl`, plus a convenience module
like `Enum`), but the semantic object is a registry fact. The pieces:

- `ProtocolCallback` / `ProtocolImpl` (`src/compiler2/protocol.rs`) — the owned
  facts: which protocol a callback belongs to, and a protocol's per-target impl.
- `ImplTarget` — the module a `defimpl` is *for*, mapped to a concrete type when
  dispatch is checked.
- `resolve_protocol_call` (`jobs/semantic.rs`) — selects the impl at a callsite from
  receiver type facts.

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

`defprotocol Enumerable` publishes a first-class namespace at its lexical path (a
root declaration publishes `Enumerable`, not `Enumerable.Enumerable`). It owns the
required callback names/arities and their public specs. `defimpl` declares the
protocol, the target, and the callback bodies; the callbacks lower into a
**protocol-owned** module named `protocol.child(target)` — `defimpl Enumerable, for:
List` produces `Enumerable.List.reduce/3` (`reference_protocol_impl_module`), not a
function on `List`, so the body can delegate to ordinary target helpers like
`List.reduce/3` without colliding.

The runtime library follows Elixir's split: `Enumerable` is the protocol; `Enum` is
the convenience module users call. Low-level control tuples
(`{:cont|:halt|:suspend, acc}`) stay on `Enumerable.reduce/3`; `Enum.reduce/2,3`
returns plain accumulator values.

## The owned facts

`World` carries two registries:

- **`ProtocolCallbackMap`** — `function -> ProtocolCallback { protocol }`.
  `define_protocol_callback` fills it while indexing a `defprotocol` surface, so a
  callback function knows the protocol it answers to.
- **`ProtocolImplMap`** — `ProtocolImplKey { protocol, target } -> ProtocolImpl`,
  where a `ProtocolImpl` maps each `(name, arity)` to a
  `ProtocolCallbackImpl { function, owner_module }`. `define_protocol_impl` fills it
  while indexing a `defimpl`.

`protocol_callback(fn)` answers "is this function a protocol callback?". It reads the
registry, and `derived_protocol_callback` covers a function in a module indexed as
`ModuleSourceKind::Protocol`. That is how runtime protocols such as `Enumerable` are
recognized without a user `defprotocol` in the program.

## Implementation targets

An `ImplTarget` is a module identity, never a display string. `impl_target_ty` maps a
target's last segment to a concrete type:

```text
List -> list(any)   Integer -> int   Float -> float   Atom -> atom
Binary -> str       Map -> map_top    <other> -> struct_impl_target_type(name)
```

A named source struct (e.g. `Range`) maps to its nominal opaque tag
`opaque(impl-target::Range)` over its field tuple (see
[`set-theoretic-types`](set-theoretic-types.md)), which keeps it distinct from any
structurally-similar value.

## Dispatch is receiver-subtype selection, pulled by demand

A protocol callsite is an ordinary call whose callee is a protocol callback function.
When `resolve_function_call` sees `protocol_callback(fn)`, it hands off to
`resolve_protocol_call`, which selects an implementation from the receiver type — the
first argument:

```text
receiver = input_types[0]
for each registered (protocol, target) impl:
    if is_subtype(receiver, impl_target_ty(target)) and it has this callback:
        collect it
exactly one match  -> activate that impl callback as an ordinary call
                      (the protocol callsite becomes a direct call to the impl)
no match           -> pull the runtime impl module whose target the receiver fits,
                      then stay unresolved (any) and retry
many matches       -> unresolved (any): the receiver is open/ambiguous here
```

Selection is **minimal**: it asks about the concrete type that actually arrived, not
about the full set of implementers. When no registered impl matches, the job asks
`runtime_impl_target_modules(receiver)` for the runtime module whose target the
receiver fits and `wait_for_runtime_module`s it, so only that owning source is pulled
and indexed; the retry then finds the impl. A single match waits for the impl's
`owner_module` to be defined, then activates `selected.function` through the ordinary
call path — so a known list receiver at `Enumerable.reduce/3` resolves to
`Enumerable.List.reduce/3` and the callsite summary names that concrete callee, no
stub and no runtime lookup table. An impl callback is an ordinary function: only the
callbacks a reachable callsite selects are activated and lowered; the rest stay cold,
and an impl for a type no value ever presents is never pulled at all.

## The domain marker

`Protocol.t(...)` resolves to a nominal **domain marker** — the protocol's opaque
domain tag, element-parametric — and nothing more. It is a `TypeDefined` fact that
depends only on the protocol declaration (see [`type-naming`](type-naming.md)), never
on the impl set, so it settles at the surface tier and never widens as the program is
analyzed. The element parameter is a real refinement carried structurally:
`Enumerable.t(integer)` instantiates the element variable, refining an
element-parametric target.

Whether a concrete type *is in* the domain is not read off the marker's structure —
it is the same demand-driven dispatch question above. A spec parameter typed
`Enumerable.t(a)` is satisfied at a callsite when the argument's concrete type has an
implementation, which the dispatch path proves by pulling that one impl; an argument
whose type has no implementation is a use-site error surfaced when the drive goes
quiet. So the domain marker names the requirement, and dispatch discharges it against
exactly the types that flow — never an eager union over every implementer.

## Callback surface vs domain

The two are checked in different places. The **callback surface** is validated at
implementation time: an impl must define every required callback at the required
arity and none the protocol never declared, and when both protocol and impl carry
`@spec`s their arrows are compared per position, rejecting only on proved
set-theoretic disjointness (so free variables and `any` never false-positive). The
**domain** is discharged at use sites: a spec requiring `P.t(...)` is satisfied when
the argument's concrete type has an implementation to pull.

## Closed but minimal

A protocol's implementation relation is **closed**: for any concrete type and
protocol, "is there an impl?" has a fixed answer determined by the program text,
with no dynamic registration. That is what makes a dispatch demand terminate with a
definite yes or no. It does *not* mean the implementers are enumerated up front —
the program only ever asks the question for types that actually reach a protocol
position, and only the impls it asks about (and the callbacks it calls) are pulled
into the program. Closed in principle; minimal in practice.

## Where the facts live

```text
jobs/source.rs   indexes defprotocol (define_protocol_surface ->
                 define_protocol_callback) and defimpl (define_protocol_impl);
                 reference_protocol_impl_module names the protocol.child(target) module
compiler2/protocol.rs  the ProtocolCallback / ProtocolImpl fact shapes + maps
world.rs         define/read protocol facts; impl_target_ty; runtime_impl_target_modules
jobs/semantic.rs resolve_protocol_call — the receiver-subtype selection above
```

## Proof gates

```text
cargo test --lib compiler2::drive_test::compiler2_enum_reduce_selects_list_protocol_impl_and_callable_reducer
cargo test --lib compiler2::drive_test::compiler2_materialization_freezes_only_the_selected_enum_reduce_path
cargo test --test fixture_matrix enumerable_protocol_dispatch
```
