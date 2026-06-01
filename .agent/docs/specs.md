# Specs

`@spec` declarations are function contracts. The spec subsystem owns the
resolved contract model and the operations that interpret it: scheme matching,
overload selection, declared-call application, structural correspondence, and
declared-vs-inferred coverage.

`type_expr` resolves source syntax into this model. `types` supplies the
set-theoretic algebra and structural queries. Consumers call `crate::specs`;
they do not implement their own spec semantics.

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
function input arrow to return `[{a, integer}]`. Spec application selects
compatible arrows first and unions only their successful results.

## Resolved Model

`src/specs/model.rs` owns the resolved shapes:

- `ResolvedSpecSet` is the ordered overload set.
- `ResolvedSpec` stores concrete `params`, concrete `result`, structural
  `param_shapes`, structural `result_shape`, and type-variable `constraints`.
- `ResolvedTypeShape` is the non-lossy structural form used to recover where
  declared type variables occur across params, results, nested containers,
  structs, and callback arrows.
- `StructuralCorrespondenceGroup` records repeated type-variable occurrences
  as paths through the structural shapes.

The concrete `Ty` fields are the facts used for subtype and disjointness
decisions. The structural shapes are the facts used for declared
parametricity. A contract such as:

```fz
@spec reduce(Enumerable.t(a), b, (a, b) -> b) :: b
```

keeps every occurrence of `a` and `b` visible even when a concrete execution
type no longer exposes that relationship directly.

Lowering persists declared specs in `Module.declared_specs:
HashMap<FnId, ResolvedSpecSet>`. It persists structural correspondence in
`Module.function_correspondence`, keyed by the same `FnId`, so planner and CPS
rewrites consume the spec-layer fact instead of rediscovering it.

## Engine Pieces

`src/specs/mod.rs` is the crate-facing API. The modules behind it are private
implementation detail unless a production caller needs a named result type.

- `model.rs` defines resolved spec data and structural correspondence paths.
- `match.rs` instantiates a scheme from witness types and returns
  `Known`, `Underconstrained`, or `Invalid`.
- `apply.rs` applies a `ResolvedSpecSet` to a call's argument facts and returns
  `SpecApplicationOutcome`.
- `select.rs` computes structural correspondence groups and, when exactly one
  arrow matches, the instantiated parameter demand.
- `validate.rs` checks whether a declared overload set covers one inferred
  narrow behavior.

`type_expr::resolve_spec_decls` is the construction seam from source syntax to
`ResolvedSpecSet`. After construction, spec consumers use `crate::specs`
operations.

## Scheme Matching

Scheme matching is evidence-driven. `instantiate_match` receives declared
parameter patterns, a declared result pattern, constraints, and callsite
witness types. It collects a type-variable substitution structurally, applies
constraints, then instantiates params and result.

The matcher distinguishes three outcomes:

```text
Known(T)             all result variables are determined by witnesses
Underconstrained(T)  some variables remain after substitution
Invalid              arity, shape, constraint, or subtype checks failed
```

Witness collection uses the positive evidence in tuples, lists, resources,
maps, callable arrows, and direct variable occurrences. A positional hole in
validation is unknown evidence, not an `any` witness. `any` is a value in the
type lattice; the matcher does not invent it to cover missing proof.

## Spec Application

`apply_spec_set` is the declared-call typing seam. It takes a
`ResolvedSpecSet`, argument facts, and a callback-return resolver supplied by
the caller. It returns:

```text
Known(application)            selected arrows produced executable result facts
Underconstrained(application) selected arrows exist, but proof is incomplete
NoMatch                       arguments are proved incompatible with every arrow
```

For broad inputs, application uses successful overlap witnesses. For example,
`any + integer` does not become `any`, and it does not become `none` unless no
successful arrow exists. It selects the arrows with non-empty overlap and
unions their successful returns. A proved contradiction returns `NoMatch`; an
unresolved proof returns `Underconstrained`.

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
`CallbackReturnFact` through `CallbackReturnQuery`.

Planner callers translate that query into a `SpecKey` read. A known callback
return refines the witness for the higher-order argument. A pending callback
return records the read and marks the application incomplete, allowing the
worklist to revisit the caller when the callback return settles.

This is the load-bearing path for contracts such as:

```fz
@spec reduce_while(Enumerable.t(a), b, (a, b) -> {:cont, b} | {:halt, b}) :: b
```

The initial accumulator witnesses `b`, and the reducer's successful
`{:cont, b}` / `{:halt, b}` returns also witness `b`. The result is the union
of successful accumulator shapes, not the initial accumulator frozen at the
first callsite.

## Consumers

The frontend spec checker resolves source specs, finds inferred planner facts,
and renders diagnostics. The semantic coverage rule lives in
`declared_specs_cover_inferred_spec`.

The planner and codegen use `apply_spec_set` for declared-call return facts.
Planner callback queries become `SpecKey` reads at the planner boundary.
Codegen uses the same application result to choose ABI-facing return shapes.

IR walking uses `unique_matching_params` only for the selected-arrow case.
Protocol callbacks and module interfaces store ordered spec lists, so
overloaded public contracts survive `.fzi` artifacts and fingerprinting.

## Proof Gates

Gate changes to this model with:

- `cargo check --lib`
- `cargo test --lib specs -- --nocapture`
- `cargo test --lib type_infer -- --nocapture`
- `cargo test --lib frontend::spec_check -- --nocapture`
- `cargo test --test fixture_matrix spec_`
- `cargo test --test fixture_matrix enum_map_family`
- `cargo test --test fixture_matrix multi_caller_spec_divergent`
- `cargo test --test fixture_matrix closure_typed_captures`

The focused `specs` tests cover `Known`, `Underconstrained`, and `Invalid`
matching, overload correlation, coverage holes, successful-overlap returns,
proved no-match, and higher-order callback-return refinement. The fixture
matrix proves the same contracts through production drivers and telemetry
budgets where fixture shape is the observable signal.
