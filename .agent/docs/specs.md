# Specs

`@spec` declarations are function contracts. The `src/specs` engine owns the
resolved contract model and the operations that interpret it: scheme matching,
overload selection, declared-call typing, structural correspondence, closure
return resolution, and declared-vs-inferred coverage.

`type_expr` resolves source syntax into this model. `types` supplies the
set-theoretic algebra and structural queries (subtype, intersect, instantiate,
`callable_clauses`, tuple/list/map/resource projections). Consumers call
`crate::specs` for spec semantics; they do not reimplement them.

The pieces a reader should hold in their head:

- a **resolved model** (`model.rs`): the overload set plus the structural shapes
  that record where type variables live.
- a **scheme matcher** (`match.rs`): instantiate a contract from witness types,
  reporting `Known` / `Underconstrained` / `Invalid`.
- a **spec applicator** (`apply.rs`): apply a whole overload set to a call's
  arguments, including higher-order callback returns, and produce return facts.
- **selection + coverage helpers** (`select.rs`, `validate.rs`): correspondence
  groups, single-arrow parameter demand, and the upper-bound coverage check.

## Overload Sets

A function can have several spec arrows for the same name and arity:

```fz
@spec with_index(Enumerable.t(a), integer) :: [{a, integer}]
@spec with_index(Enumerable.t(a), (a, integer) -> b) :: [b]
fn with_index(enumerable, fun_or_offset)
```

Those arrows form one ordered `ResolvedSpecSet`:

```rust
pub(crate) struct ResolvedSpecSet {
    pub arrows: Vec<ResolvedSpec>,
}
```

Each arrow preserves its own parameter-to-result correlation. The equivalent
union-shaped declaration answers a different question:

```fz
@spec with_index(Enumerable.t(a), integer | ((a, integer) -> b)) ::
  [{a, integer}] | [b]
```

That shape permits the integer input arrow to return `[b]`, and permits the
function input arrow to return `[{a, integer}]`. Application keeps arrows
separate: it selects compatible arrows and unions only their successful results.

## Resolved Model

`model.rs` owns the resolved shapes:

- `ResolvedSpecSet` is the ordered overload set.
- `ResolvedSpec` stores concrete `params` (`Vec<Ty>`), concrete `result`
  (`Ty`), structural `param_shapes`, structural `result_shape`, and
  type-variable `constraints` (`HashMap<TypeVarId, Ty>`, serialized as a
  sequence because the numeric key is not a valid JSON object key).
- `ResolvedTypeShape` is the non-lossy structural form. Its variants
  (`Var`, `List`, `Tuple`, `Arrow`, `Resource`, `Named`, `Union`,
  `StructRecord`, the scalar leaves) let the engine recover where declared type
  variables occur across params, results, nested containers, structs, and
  callback arrows.
- `StructuralCorrespondenceGroup { var, occurrences }` records repeated
  type-variable occurrences as `StructuralOccurrence`s (`Param`, `Result`,
  `CallbackArg`, `CallbackResult`), each carrying a path of
  `StructuralPathStep`s through the structural shapes.

The concrete `Ty` fields are the facts used for subtype and disjointness
decisions. The structural shapes are the facts used for declared parametricity.
A contract such as:

```fz
@spec reduce(Enumerable.t(a), b, (a, b) -> b) :: b
```

keeps every occurrence of `a` and `b` visible even when a concrete execution
type does not expose that relationship directly.

The IR `Module` (in `src/fz_ir`) holds the spec-layer facts so downstream
passes consume them instead of rediscovering them:

```rust
pub declared_specs: HashMap<FnId, ResolvedSpecSet>,
pub function_correspondence: HashMap<FnId, Vec<StructuralCorrespondenceGroup>>,
```

Lowering fills both from `@spec` (continuations also contribute synthesized
correspondence groups from lowering provenance).

## Engine Pieces

`mod.rs` is the crate-facing API; the modules behind it are private detail
except for the result types a production caller names.

- `model.rs` defines resolved spec data and structural correspondence paths.
- `match.rs` instantiates a scheme from witness types and returns
  `SchemeInstantiation::{Known, Underconstrained, Invalid}`. It also exports
  `resolve_closure_return`.
- `apply.rs` applies a `ResolvedSpecSet` to a call's argument facts and returns
  `SpecApplicationOutcome`.
- `select.rs` computes structural correspondence groups
  (`spec_set_correspondence_groups`) and, when exactly one arrow matches, the
  instantiated parameter demand (`unique_matching_params`).
- `validate.rs` checks whether a declared overload set covers one inferred
  narrow behavior (`declared_specs_cover_inferred_spec`).

`type_expr::resolve_spec_decls` is the construction seam from source syntax to
`ResolvedSpecSet`. After construction, callers use `crate::specs` operations.

The matcher (`match.rs`) is generic over the `ClosureTypes` trait's associated
`Ty`, so the same scheme-instantiation code runs over both the concrete and
interned representations. Application, selection, and coverage (`apply.rs`,
`select.rs`, `validate.rs`) are pinned to the concrete `Ty`
(`ClosureTypes<Ty = Ty>`).

## Scheme Matching

Scheme matching is evidence-driven. `instantiate_match` receives declared
parameter patterns, a declared result pattern, constraints, and callsite
witness types. It collects a type-variable substitution structurally, applies
constraints, then instantiates params and result.

The matcher distinguishes three outcomes:

```text
Known(T)             all result variables are determined by witnesses
Underconstrained(T)  some result variable remains after substitution
Invalid              arity, shape, constraint, or subtype checks failed
```

Witness collection merges the positive evidence found in tuples, lists,
resources, maps, callable arrows, and direct variable occurrences. Evidence is
three-valued: a structural mismatch against a concrete witness is `Invalid`; a
position that yields no binding is `Unknown`; a binding is `Known`. A witness
slot may be absent (`KeySlot` is `Option<Ty>`): an absent slot is unknown
evidence, contributing no binding. `any` is a value in the type lattice; the
matcher does not invent it to cover a missing proof.

`resolve_closure_return` is the partner operation for closure calls. Given a
closure type, an effective-returns table keyed by `(ClosureTarget, captures ++
args)`, and the call's argument types, it walks each callable clause: a
closure-literal clause looks up the table (returning `None` when that entry is
not yet ready, i.e. a pending read), a plain arrow clause with type variables is
instantiated, and an arrow with no variables uses its declared return. A closure
with no readable clauses resolves to `any`. The planner-side wrapper translates
its own `BodyKey`-keyed `effective_returns` into the closure-target table this
function expects.

## Spec Application

`apply_spec_set` is the declared-call typing seam. It takes a `ResolvedSpecSet`,
argument facts, and a callback-return resolver supplied by the caller. It
returns:

```text
Known(application)            selected arrows produced executable result facts
Underconstrained(application) selected arrows exist, but proof is incomplete
NoMatch                       arguments are proved incompatible with every arrow
```

`SpecApplicationOutcome` is generic over a read type `R`: each matched arrow
carries the reads it performed and whether it is `complete`, so an incremental
caller can revisit the call when a pending read settles.

Each arrow first tries a direct instantiation against the raw arguments. When
that is underconstrained or invalid, it retries with **overlap witnesses**: the
intersection of each declared param with its argument, rejecting the arrow if
any intersection is empty. So `any + integer` against an `integer` param
witnesses `integer`, not `any`. Application unions the successful (`Known`)
returns of the arrows that matched.

If no arrow yields a known result but some arrow matched or some argument still
carries type variables, the outcome is `Underconstrained`. Only a proved
contradiction — no arrow matched and no argument is unresolved — is `NoMatch`.
A return therefore becomes `none` only when no successful arrow exists.

Call-input demand is stricter than return selection. `unique_matching_params`
returns instantiated parameter demand only when exactly one arrow matches.
When several arrows match, the caller keeps the concrete call arguments as the
demand so unrelated overload params do not collapse into a parameter union.

## Higher-Order Evidence

A closure argument has two separate facts:

```text
closure value      target plus captures
callback return    effective return for that target at a demanded argument key
```

`apply_spec_set` keeps those facts separate. It instantiates each candidate
arrow from ordinary argument witnesses first. If a higher-order parameter's
declared callback result contains a type variable, it asks the caller for a
`CallbackReturnFact` through a `CallbackReturnQuery { target, captures, args,
demand }`. The `demand` is `CallbackReturnDemand::Value`, or `TupleFields(arity)`
when the declared callback result is a tuple, so a tuple-returning reducer is
queried per field.

The resolver answers with `CallbackReturnFact::Known { result, read, complete }`
or `Pending { read }`. A known callback return refines the witness for the
higher-order argument (the matched arrow's args plus the resolved result). A
pending callback return records the read and marks the application incomplete.

Planner callers translate a `CallbackReturnQuery` into a `SpecKey` read: they
build the callee's fixed-point spec key from captures, args, and the demand,
then look up its result slot. `R` is therefore `SpecKey` on the planner path,
and `()` on the non-incremental paths that pass a resolver returning `None`.

This is the load-bearing path for contracts such as:

```fz
@spec reduce_while(Enumerable.t(a), b, (a, b) -> {:cont, b} | {:halt, b}) :: b
```

The initial accumulator witnesses `b`, and the reducer's successful
`{:cont, b}` / `{:halt, b}` returns also witness `b`. The result is the union
of successful accumulator shapes, not the initial accumulator frozen at the
first callsite.

## Consumers

The frontend spec checker (`frontend::spec_check`) resolves each `@spec` against
its `ModuleTypeEnv`, finds the inferred narrow specs the planner registered in
`ModulePlan.specs` for that fn, and renders `spec/violation` diagnostics. A
declared `@spec` is an **upper bound**: the semantic rule
`declared_specs_cover_inferred_spec` passes when the inferred result is a
subtype of some declared arrow's instantiated result. All-`any` any-key specs
are planner-internal fallbacks and are skipped.

`apply_spec_set` has three consumers:

- The **planner worklist** computes declared-call return facts, with callback
  queries resolved to `SpecKey` reads.
- **Planner reachability** computes declared-call returns during reachability,
  with a resolver that returns `None`.
- **Type inference** uses a declared `@spec` as a backstop: only when body
  inference is `Unknown` does it instantiate the spec against the inputs, so an
  inferable body keeps its (usually tighter) inferred type.

Codegen and materialization do not apply spec sets. They consume the planner's
already-resolved specs through the `SpecRegistry`; linking copies
`declared_specs` and `function_correspondence` into the linked module.

IR walking uses `unique_matching_params` only for the selected-arrow case.
Protocol callbacks and module interfaces store ordered spec lists
(`Vec<InterfaceSpec>`), so overloaded public contracts survive compiler-owned
module contracts and interface fingerprinting.

## Tests

The focused `specs` unit tests cover `Known`, `Underconstrained`, and `Invalid`
matching, overload return correlation, coverage acceptance and holes,
successful-overlap returns, proved no-match, and pending/refined higher-order
callback returns (including `reduce_while` accumulator widening). `type_infer`
and `frontend::spec_check` tests cover the backstop and the coverage diagnostic.

The fixture matrix proves the same contracts through production drivers, where
fixture shape and telemetry budgets are the observable signal: `spec_ok`,
`spec_boundary`, `spec_violation`, `enum_map_family`,
`multi_caller_spec_divergent`, and `closure_typed_captures`.
