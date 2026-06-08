# Protocols

A protocol is a typed compiler fact, not a generated dispatch module. It bundles
two things:

- a **callback surface** — the function names and arities an implementation must
  provide;
- a **domain type** — `Protocol.t(...)`, the set of values known to have an
  implementation.

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
`opaque(impl-target::Range)` over its field tuple (see
[`set-theoretic-types`](set-theoretic-types.md)), which keeps it distinct from
any structurally-similar value.

## Dispatch is receiver-subtype selection

A protocol callsite is an ordinary call whose callee is a protocol callback
function. When `resolve_function_call` sees `protocol_callback(fn)`, it hands off
to `resolve_protocol_call`, which selects an implementation from the receiver
type — the first argument:

```text
receiver = input_types[0]
for each registered (protocol, target) impl:
    if is_subtype(receiver, impl_target_ty(target)) and it has this callback:
        collect it
exactly one match  -> activate that impl callback as an ordinary call
                      (the protocol callsite becomes a direct call to the impl)
no match           -> pull reachable runtime impl modules whose target the
                      receiver is a subtype of, then stay unresolved (any) and retry
many matches       -> unresolved (any): the receiver is open/ambiguous here
```

Selection is lazy about runtime code: when no registered impl matches, the job
asks `runtime_impl_target_modules(receiver)` for the runtime modules whose target
the receiver fits and `wait_for_runtime_module`s each one, so the owning runtime
source is pulled and indexed; the retry then finds the impl. A single match
waits for the impl's `owner_module` to be defined, then activates
`selected.function` through the ordinary call path — so a known list receiver at
`Enumerable.reduce/3` resolves to `Enumerable.List.reduce/3` and the callsite
summary names that concrete callee, no stub and no runtime lookup table.

## The domain type

`Protocol.t(...)` is the union of each implementing target's type (with the
protocol's opaque domain tag), not `any`. It is the type a declared spec uses to
require "a value with an implementation": a spec parameter typed
`Enumerable.t(a)` rejects an `Integer` because `Integer` is disjoint from the
domain union. The element parameter is a real refinement — `Enumerable.t(integer)`
refines an element-parametric target like `List` to `list(integer)`. The domain
alias is resolved by `type_expr` and checked through the ordinary spec coverage
rule (see [`specs`](specs.md)); runtime dispatch instead matches the receiver
against impl-target types directly.

## Callback surface vs domain

The two are checked in different places. The **callback surface** is validated at
implementation time: an impl must define every required callback at the required
arity and none the protocol never declared, and when both protocol and impl carry
`@spec`s their arrows are compared per position, rejecting only on proved
set-theoretic disjointness (so free variables and `any` never false-positive).
The **domain type** is checked at use sites: a spec requiring `P.t(...)` needs
proof the argument is inside `P`'s domain.

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
