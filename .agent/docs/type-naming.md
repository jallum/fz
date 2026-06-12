# Type Naming

A type name in source — `integer`, `pair`, `Enumerable.t`, `SomeModule.t` — is a
*name*, not a type. Naming a type and representing one are two jobs in two places.
`Types` represents: it mints and compares set-theoretic symbols and knows nothing
about what the language calls them (see [`type-world`](type-world.md)). This
subsystem names: it turns a source name into a stable identity, resolves that
identity to a hard `Ty`, and publishes the answer as a fact every consumer reads.

The shape in one line:

```text
name → (namespace) → identity → (fact) → Ty
```

It is the same path a value name takes — `Var("Enum")` → `ModuleId` →
`ModuleDefined` — applied to types.

## The three pieces

- **Namespace is the bridge.** A type-position name resolves through the same
  binding chain that resolves value names (see [`modules`](modules.md)).
  `NamespaceSymbol::Type(TypeName)` binds a type name to its identity, exactly as
  `Function(FunctionId)` binds a call name to its identity. The chain binds a name
  to an *identity*, never to a resolved type, so a name can be bound before the
  type behind it is known.
- **`TypeName` is the identity:** `(ModuleId, name, arity)`. It is minted on
  reference and may be named before it is defined. Keying on the owning `ModuleId`
  rather than a dotted string means `t` resolved inside `SomeModule` and
  `SomeModule.t` resolved from outside land on one identity, and a module alias
  never changes it. Arity is part of the identity — `t/0` and `t/1` are different
  names.
- **`TypeDefined(TypeName)` is the fact.** Its payload — the resolved `Ty`, or a
  parameterized template — lives in a typed store keyed by `TypeName`; the fact
  itself carries `Presence(revision)`, the same store/fact split lowering and
  contracts use (see [`fact-engine`](fact-engine.md)). `DeriveTypeDef` reads the
  declaring module's `@type` body, mints the symbol once, and publishes it.

## Reference before define

Recording a spec does not require its type names to be resolved.

```fz
@spec foo(SomeModule.t(float), integer) :: integer
```

Scoping `foo` resolves the module path through the namespace, mints
`SomeModule`'s `ModuleId` and the identity `TypeName(SomeModule, "t", 1)`, and
records that identity in the function's type-reference wait set. Nothing is
resolved yet, and nothing needs to be. `DeriveFunctionContract(foo)` waits on
`TypeDefined(SomeModule, "t", 1)`; once it and every other type name in the spec
are present, compiler2 resolves the spec against the namespace captured on the
function definition and publishes `FunctionContract(foo)` (see
[`specs`](specs.md)). Knowing a function's spec before processing it is just:
the contract is a fact with upstream facts. A name whose arity at the use site
disagrees with its definition, or that no module ever defines, is an
unresolved-frontier diagnostic surfaced when the drive goes quiet — the same
machinery as an unknown import.

## Naming settles below the semantic frontier

Type denotation is a **surface-tier** fact. It depends only on indexing and
definition — never on activations, return types, or callsite summaries. The tiers,
and the one-way rule between them:

```text
INDEX     CodeIndexed, ModuleIndexed
SURFACE   CodeScoped, ModuleDefined, FunctionSource, FunctionDefined,
          TypeDefined, ProtocolDispatch, FunctionContract, LoweredBody,
          EntryDispatch, …
SEMANTIC  Activation, Executable, ReturnType, CallSiteSummary, SemanticClosed
ARTIFACT  MaterializedProgram → AbiReady → …
```

Every dependency edge points down this list. By the time the fixpoint loop runs
(see [`semantic-fixpoint`](semantic-fixpoint.md)) every type name is already a hard
`Ty`. The semantic tier *reads* types; it never moves a denotation. That one-way
rule is what lets `SealSemanticClosure` observe a frontier whose types are settled
rather than chase one that is still resolving.

## A name resolves to a self-contained symbol

`DeriveTypeDef` mints the *complete* symbol once, so the answer needs no follow-up
lookups. A brand `@type Meters :: refines integer` mints
`mint_brand(integer, "M::Meters")` — a `Ty` whose own axes already carry the inner
representation (see [`set-theoretic-types`](set-theoretic-types.md)). At a use
site, `is_subtype(Meters, integer)` reads from that symbol's structure; no name
table is threaded into the lattice. The definition fact is the single place a name
becomes a symbol, so it is the single place the inner is established.

## Protocol domains are markers, not unions

A protocol name in type position — `Enumerable.t`, `SomeModule.t` — resolves to a
nominal **domain marker**: an opaque tag for "the protocol's domain," and nothing
more. Protocol publication notes `t/0` and `t/1` as normal type declarations;
`DeriveTypeDef` resolves both to the same protocol-owned marker. The marker
depends on the protocol declaration, never on the impl set. *Which*
implementations a program contains is a dispatch fact and a reachability question,
answered as concrete values flow to protocol positions, not a property baked into
the domain type (see [`protocols`](protocols.md)). A program that never mentions
a `Range` never pulls the `Range` impl, and only the callbacks actually called are
lowered. The domain's meaning is fixed at the surface tier; the reached impl set
accretes at the semantic tier the same way any reached function does.

## Where it lives

```text
namespace.rs       NamespaceSymbol::Type(TypeName) — the bridge
identity.rs        TypeName { module, name, arity }; NotedTypeDecl captures
                   the parsed body and the namespace where it appeared
type_expr.rs       compiler2-owned syntax parser; names stay bare TypeExpr::Name
resolve.rs         classifies names against the captured Namespace, reads
                   TypeDefined stores, and mints hard Ty through World.types
source_publish.rs  notes @type declarations, binds NamespaceSymbol::Type, and
                   records exact TypeDefined wait sets for @type/@spec/extern
drive.rs           FactKey::TypeDefined(TypeName); Job::DeriveTypeDef(TypeName)
jobs/types.rs      derive_type_def — wait on referenced TypeDefined facts,
                   resolve the noted body, publish TypeDefined
jobs/contract.rs   derive_function_contract — wait on function TypeDefined refs,
                   resolve @spec/extern contracts, publish FunctionContract
```

## Proof gates

The behavior is observed through the drive telemetry, not through the resolver
internals:

```text
cargo test --lib compiler2::drive_test::compiler2_enum_reduce_selects_list_protocol_impl_and_callable_reducer
cargo test --lib compiler2::drive_test::compiler2_materialization_freezes_only_the_selected_enum_reduce_path
cargo test --lib compiler2::world_test::compiler2_resolve_spec_resolves_types_shapes_and_constraints_against_the_captured_namespace
cargo test --test fixture_matrix enumerable_protocol_dispatch
cargo test --lib specs::          # scheme matching over the resolved model
```
