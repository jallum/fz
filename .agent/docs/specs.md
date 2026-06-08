# Specs

`@spec` declarations are function contracts. `src/specs` is the semantic engine
that interprets the resolved contract model: scheme matching, overload-set
application, structural correspondence, and declared-vs-inferred coverage. It is
a pure engine — it returns structured outcomes and leaves diagnostics to its
caller.

The split of duties:

- `type_expr::resolve_spec_decls` resolves source `@spec` syntax into the
  `ResolvedSpecSet` model (the construction seam).
- `crate::specs` owns the operations over that model.
- `crate::types` supplies the set-theoretic algebra the operations decide on
  (subtype, intersect, instantiate, projections — see
  [`set-theoretic-types`](set-theoretic-types.md)).

Scheme matching is generic over the type trait, so it runs over either type
kernel; the application and coverage helpers are written against the concrete
`Ty`.

## Overload sets

A function can carry several spec arrows for the same name and arity:

```fz
@spec with_index(Enumerable.t(a), integer) :: [{a, integer}]
@spec with_index(Enumerable.t(a), (a, integer) -> b) :: [b]
fn with_index(enumerable, fun_or_offset)
```

Those arrows form one ordered `ResolvedSpecSet { arrows: Vec<ResolvedSpec> }`.
Each arrow preserves its own parameter-to-result correlation, which the
union-shaped declaration would lose. Application selects compatible arrows and
unions only their successful results, so the integer-input arrow cannot return
the function-input arrow's result.

## Resolved model

`model.rs` owns the resolved shapes:

- `ResolvedSpec` stores concrete `params` and `result` (`Ty`), the structural
  `param_shapes`/`result_shape`, and type-variable `constraints`.
- `ResolvedTypeShape` is the non-lossy structural form (`Var`, `List`, `Tuple`,
  `Arrow`, `Resource`, `Named`, `Union`, `StructRecord`, scalar leaves). It lets
  the engine recover where declared type variables occur across params, results,
  nested containers, structs, and callback arrows.
- `StructuralCorrespondenceGroup { var, occurrences }` records each repeated
  type-variable occurrence (`Param`, `Result`, `CallbackArg`, `CallbackResult`)
  with a path of `StructuralPathStep`s.

The concrete `Ty` fields drive subtype/disjointness decisions; the structural
shapes drive declared parametricity. A contract such as
`@spec reduce(Enumerable.t(a), b, (a, b) -> b) :: b` keeps every occurrence of
`a` and `b` visible even when an execution type does not expose the relationship
directly.

## Engine pieces

`mod.rs` is the crate-facing API; the modules behind it are private detail except
the result types a caller names.

- `match.rs` — `instantiate_match` instantiates a scheme from witness types and
  returns `SchemeInstantiation`. It also exports `resolve_closure_return`.
- `apply.rs` — `apply_spec_set` applies a whole `ResolvedSpecSet` to a call's
  argument facts, including higher-order callback returns, and returns a
  `SpecApplicationOutcome`.
- `select.rs` — `spec_set_correspondence_groups`, and `unique_matching_params`
  (instantiated parameter demand when exactly one arrow matches).
- `validate.rs` — `declared_specs_cover_inferred_spec`, the upper-bound coverage
  check.

## Scheme matching

`instantiate_match` collects a type-variable substitution structurally, applies
constraints, then instantiates params and result. Evidence is three-valued — a
structural mismatch against a concrete witness is `Invalid`, a position with no
binding is `Unknown`, a binding is `Known` — and an absent witness slot
contributes no binding. `any` is a value in the lattice; the matcher never
invents it to cover a missing proof.

```text
Known(T)             all result variables determined by witnesses
Underconstrained(T)  some result variable remains after substitution
Invalid              arity, shape, constraint, or subtype checks failed
```

`resolve_closure_return` is the partner for closure calls: given a closure type,
an effective-returns table, and the call's argument types, it walks each callable
clause (a closure-literal clause looks up the table — returning `None` for a
not-yet-ready entry; an arrow clause instantiates or uses its declared return; a
closure with no readable clauses resolves to `any`).

## Spec application

`apply_spec_set` is the declared-call typing seam. Each arrow first tries a
direct instantiation against the raw arguments; when that is underconstrained or
invalid it retries with **overlap witnesses** — the intersection of each declared
param with its argument, rejecting the arrow on an empty intersection. So
`any + integer` against an `integer` param witnesses `integer`, not `any`.
Application unions the `Known` returns of the arrows that matched.

```text
Known(application)            selected arrows produced executable result facts
Underconstrained(application) selected arrows exist, but proof is incomplete
NoMatch                       arguments are proved incompatible with every arrow
```

Only a proved contradiction — no arrow matched and no argument is unresolved — is
`NoMatch`; a return becomes `none` only then. `SpecApplicationOutcome` is generic
over a read type `R`: each matched arrow carries the reads it performed and
whether it is `complete`, so an incremental caller can revisit the call when a
pending read settles.

Call-input demand is stricter than return selection. `unique_matching_params`
returns instantiated parameter demand only when exactly one arrow matches; when
several match, the caller keeps the concrete call arguments as the demand so
unrelated overload params do not collapse into a parameter union.

## Higher-order evidence

A closure argument carries two separate facts:

```text
closure value      target plus captures
callback return    effective return for that target at a demanded argument key
```

`apply_spec_set` keeps them separate. It instantiates each candidate arrow from
ordinary argument witnesses first; if a higher-order parameter's declared
callback result contains a type variable, it asks the caller for a
`CallbackReturnFact` through a `CallbackReturnQuery { target, captures, args,
demand }`. The `demand` is `Value`, or `TupleFields(arity)` when the declared
callback result is a tuple (so a tuple-returning reducer is queried per field).
A `Known { result, read, complete }` callback return refines the higher-order
argument's witness; a `Pending { read }` records the read and marks the
application incomplete.

This is the load-bearing path for contracts such as:

```fz
@spec reduce_while(Enumerable.t(a), b, (a, b) -> {:cont, b} | {:halt, b}) :: b
```

The initial accumulator witnesses `b`, and the reducer's `{:cont, b}` /
`{:halt, b}` returns also witness `b`, so the result is the union of successful
accumulator shapes — not the initial accumulator frozen at the first callsite.

## Coverage and the @spec violation check

A declared `@spec` is an **upper bound**, not a precise signature. The semantic
rule `declared_specs_cover_inferred_spec` passes when the inferred narrow result
is a subtype of some declared arrow's instantiated result. The frontend spec
checker resolves each `@spec` against its `ModuleTypeEnv`, compares it to the
function's inferred behavior, and renders a `spec/violation`
(`codes::SPEC_VIOLATION`) on a coverage gap. The check is non-fatal: it reports,
it does not block. All-`any` fallback specs are skipped.

Protocol callbacks and module interfaces store ordered spec lists so overloaded
public contracts survive interface collection and fingerprinting (see
[`protocols`](protocols.md)).

## Tests

`specs_test.rs` covers `Known`/`Underconstrained`/`Invalid` matching, overload
return correlation, coverage acceptance and holes, successful-overlap returns,
proved no-match, and pending/refined higher-order callback returns (including
`reduce_while` accumulator widening). The fixture corpus proves the same
contracts through the drivers: `spec_ok`, `spec_boundary`, `spec_violation`,
`enum_map_family`, `multi_caller_spec_divergent`, `closure_typed_captures`.
