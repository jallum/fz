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

## Types that name themselves

A `@type` that names itself, directly or through other `@type`s that name it
back, is a recursive type: `@type t :: :start | {integer, t}` is
`μt. :start | {int, t}`. Such a type cannot wait for its own `TypeDefined`, so
`DeriveTypeDef(t)` first asks `World::type_def_cycle` for the cycle `t` belongs
to: the noted declarations reachable from `t` that reach back to it. It waits
only on the `TypeDefined` and `StructDefined` facts outside the cycle, then
`World::resolve_type_cycle` opens one binder per member
(`Types::recursive_equations`), resolves every member's body with each member's
name standing for its binder, solves the bodies together
(`Types::solve_recursive`), and the job publishes its own member.

Every member's job solves the whole cycle and publishes only itself. The kernel
interns a recursive type canonically, so each job lands on the same identities,
and so does a member resolved alone against a sibling that is already
published. Which member a program pulls first therefore changes nothing
(`types_that_name_each_other_are_one_recursive_type_whichever_is_pulled_first`).
A job that runs before a sibling's module is noted sees no cycle and waits for
that sibling's `TypeDefined`; the sibling, noted later, sees the whole cycle.

A parametric member names a member only with its own parameters, in order
(`tree(a)` inside `tree(a)`): the solved body keeps them as variables, and a use
site instantiates it like any template. Any other arguments (`nest({a})` inside
`nest(a)`) wrap each unrolling once more, so no finite recursive type answers
them, and the use is refused. A member that solves to no values — `t :: t`, or
`t :: {integer, t}` with no case that ends — is refused at its declaration.
Fixtures `01357`–`01359` and `01595` run these.

## A name nothing declares

Every `TypeExpr::Name` carries the span of the name as written, the whole dotted
path, and a `%Mod{...}` record carries the span of the whole record, as a struct
literal does. A name resolution
cannot classify (a bare name nothing binds, a builtin given the wrong number of
type arguments) is refused under that span by the job resolving it. Both
`DeriveFunctionContract` and `DeriveTypeDef` fail on it, so the compile stops: a
contract is never published with one of its specs left out.

A dotted name is a `TypeDefined` wait, so one nothing declares is found at the
unresolved frontier. The reference walk (`collect_type_references` in
`source_publish.rs`) notes where each referenced name is written
(`World::note_type_reference`), and `unresolved_type_issue` reports the first
such place. When the module the name looks in was never defined, the fault is
that module, reported as `resolve/unknown-module` at the same name, and it is
the only report. Fixtures `00090` (a bare name), `00148` (a dotted name in a
module that is defined) and `01317` (a dotted name in one that is not) pin the
three reports; `a_type_name_nothing_declares_stops_the_compile_under_the_name`
and its extern/annotation sibling in `compiler2/drive_test.rs` cover each type
position.

A declaration is checked because its source wrote it, whether or not anything
reaches it. Each submission records what it declares (`SourceDeclarationMap`:
the modules it writes, the functions it defines, the `@type`s it declares).
`CheckDeclarations(owner)` (`jobs/declarations.rs`) is gated on the source's
index. It reads the indexed surface (`World::code_writes_declarations`,
`World::module_writes_declarations`) and waits on the source's own scope only
if its top level writes a `@type`, `@spec` or extern, and on a module being
defined only if that module's body writes one, so a module that declares
nothing stays cold. Then it waits on `FunctionContract` for each function that
declares a spec or is an extern, and on `TypeDefined` for each `@type`. It
publishes `DeclarationsChecked(owner)`, which a runtime root's backend product
reads before it builds the program. Nothing else demands it: a source
submitted while a root's product is retained is checked when that product is
next evaluated. So the jobs above carry the same reports
for a declaration nothing reaches, and the compile stops on every path. The
check never asks for a lowered body, so an unreached function stays cold past
its contract. Library sources are compiler-owned and are not submitted, so
their declarations stay cold too; `every_library_declaration_is_checked`
(`jobs/declarations_test.rs`) checks every library source in the test gate. Fixtures `01318` (an uncalled spec), `01319`
(an unused `@type`), `01720` (a dotted name in a module nothing uses) and
`01721` (an uncalled extern) pin it, and
`checking_an_unreached_declaration_warms_its_contract_and_nothing_else` pins
what stays cold.

## Naming settles below executable demand

Type denotation is a **surface-tier** fact. It depends only on indexing and
definition — never on activations, return types, or callsite summaries. The tiers,
and the one-way rule between them:

```text
INDEX     CodeIndexed, ModuleIndexed
SURFACE   CodeScoped, ModuleDefined, FunctionSource, FunctionDefined,
          TypeDefined, ProtocolDispatch, FunctionContract, LoweredBody,
          EntryDispatch, …
	SEMANTIC  Activation, Executable, ReturnType, CallSiteTargets, CallSiteSummary,
	          ActivationAnalyzed
	PRODUCT   MaterializedExecutable(E) → AbiExecutable(E) → BackendExecutable(E),
	          RootBackendProduct(root)
```

Every dependency edge points down this list. By the time the fixpoint loop runs
(see [`semantic-fixpoint`](semantic-fixpoint.md)) every type name is already a hard
`Ty`. The semantic tier *reads* types; it never moves a denotation. That one-way
rule is what lets product artifact producers wait on settled local semantic facts
rather than chase type names that are still resolving.

## A name resolves to a self-contained symbol

`DeriveTypeDef` mints the *complete* symbol once, so the answer needs no follow-up
lookups. A brand `@type Meters :: refines integer` mints
`mint_brand(integer, "M::Meters")` — a `Ty` whose own kind axes already carry the
inner representation, with its brand slot narrowed to the name (see
[`set-theoretic-types`](set-theoretic-types.md)). At a use
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

## Builtin constructors are one registry

A name in type position first checks a single table before anything else runs:
`resolve.rs`'s `CONSTRUCTORS`, a `&[ConstructorEntry]` mapping a builtin name to
its arity and its `Types`-minting function. This is the one authoritative
source for every builtin type-constructor name — scalars (`integer`, `boolean`,
`atom`, `binary`, `bitstring`, `map`, `tuple`, …) and the two parametric constructors (`list`, `resource`)
alike — and `classify_name` (`resolve.rs`) tries it before checking bound type
variables or the `TypeDefined` namespace. There is no separate nullary-only
table and no inline special-casing for parametric names: `list`/`list(T)` and
`resource`/`resource(T)` are ordinary registry entries with `Arity::Range(0,
1)`, resolved through the identical `find_constructor` lookup and arity check
every scalar goes through.

A structural spelling (`[T]`, `%{k => v}`, `{T, U}`) is a distinct
`TypeExpr` variant handled directly in `resolve_ty`, not a registry lookup —
but where both a name and a structural form exist for the same type (`list`
vs `[T]`, `map` vs `%{k => v}`), they mint the identical `Ty`; the registry
entry and the structural arm are proven concordant by
`resolve_test::list_bracket_and_named_forms_resolve_to_the_same_ty` and
`a_structural_map_type_resolves_to_the_same_ty_as_a_hand_built_exact_map`.
`tuple` is the nullary name for the tuple top, every tuple of every arity
(`Types::tuple_top`); `tuple(T)` is an arity error, so `{T, U}` is the only
fixed-arity spelling. `fun` is the nullary name for the function top, every
function of every arity (`Types::fun_top`), and `function` is the same type, as
in Elixir's typespecs; `fun(T)` is an arity error, so an arrow `(T -> U)` is
the only spelling of a signature.

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
cargo test --lib compiler2::drive_test::compiler2_backend_program_keeps_direct_only_enum_reduce_out_of_callable_inventory
cargo test --lib compiler2::world_test::compiler2_resolve_spec_resolves_types_shapes_and_constraints_against_the_captured_namespace
cargo test --test fixture_matrix enumerable_protocol_dispatch
cargo test --lib compiler2::types::arrow_match
```
