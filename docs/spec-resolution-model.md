# Spec Resolution Model

Status: research note for `fz-mm2.120`.

This note records the current specialization-resolution behavior across
`SpecRegistry`, `ModuleTypes`, registration order in codegen, and the
existing tests. The point is to make the semantic target explicit before
changing the data model.

## Current Sites

There are two separate "best covering spec" selectors today:

1. `SpecRegistry::resolve`
   - exact-match fast path through `lookup[fn_id][input_tys]`
   - slow path over registered keys for that `FnId`
   - cover test uses `Types::key_subsumes_with`, so the query may bind
     named type vars in the candidate key
   - ranking:
     - prefer minimum top-level var count via `Types::key_var_count`
     - then drop any candidate strictly beaten by another via
       `Types::key_is_strictly_more_specific`
     - then deterministic fallback by ascending `SpecId`

2. `ModuleTypes::effective_return_for_call_ty`
   - exact-match fast path through `effective_returns[(fn_id, key)]`
   - slow path over effective-return keys
   - cover test is plain pointwise `is_subtype`
   - ranking:
     - drop candidates strictly beaten by another with open-coded subtype checks
     - deterministic fallback by display-string ordering

These are materially different algorithms answering the same
"which specialization covers this query best?" question.

## Registration Order Today

`ir_codegen` builds the registry in two phases:

1. register any-keys first with `register_any_key_at(fn_id, any_key)`
   - this preserves the invariant `SpecId.0 == FnId.0` for surviving
     any-key specs
   - gaps are padded with sentinel slots
2. register narrow keys afterwards in deterministic order
   - sorted by `(FnId.0, format!("{:?}", key))`

So current precedence in the incomparable case is not semantic. It is a
side-effect of:

- which keys got registered at all
- the any-key-first phase
- the debug-string sort used for narrow-key registration
- the final `SpecId` tiebreak

## Current Test Contract

The tests already assert several semantic rules:

- exact match wins through the O(1) fast path
- a narrower query may dispatch to a wider registered key
- concrete keys beat var keys when both cover
- positionally inconsistent type-var bindings do not cover
- specs are isolated per `FnId`
- a saturated `any` query does not cover a concrete key

But one test encodes an incidental rule:

- subtype-incomparable covers currently pick the lowest `SpecId`

That is a property of the storage/registration scheme, not a named
resolution rule.

## Intended Direction

We are trying to approximate Elixir-style function resolution:

- resolution is per function, not global
- the candidate set is ordered
- specificity matters
- when two candidates are both applicable but incomparable, stable
  precedence still decides

For the specialization registry, that implies:

1. model a per-`FnId` specialization family explicitly
2. carry stable precedence as explicit metadata, not as an accidental
   consequence of `SpecId`
3. have one shared "best cover" selector used by both registry lookup and
   effective-return lookup
4. rewrite tests so they assert semantic precedence, not `SpecId` folklore

## Invariants To Preserve

- exact-match resolution stays O(1)
- `SpecId.0 == FnId.0` remains true for registered any-key specs
- `SpecId` stays stable for codegen/indexing consumers
- deterministic resolution remains guaranteed
- var-binding cover semantics in `SpecRegistry::resolve` are preserved

## Implementation Consequences

The next pass should likely introduce:

- `SpecEntry`
  - `spec_id`
  - `fn_id`
  - `key`
  - precomputed ranking metadata such as top-level var count
  - explicit precedence/order
- `SpecFamily`
  - exact lookup table
  - ordered entries for slow-path selection
- one named best-cover selection routine shared by:
  - `SpecRegistry::resolve`
  - `ModuleTypes::effective_return_for_call_ty`

That gives the resolution rule a real home instead of leaving it spread
across two unrelated loops over raw `Vec<Ty>` keys.
