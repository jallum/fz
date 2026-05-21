# Pattern Router Matcher ABI

Status: design for `fz-puj.15`; implementation starts in `fz-puj.16`.

The pattern router now has one source of truth:

```text
Matrix -> Decision -> lowering
```

Today `lower_decision_to_current_fn` emits the Decision tree directly into
the current function. The next step is to lower that same Decision into an
internal matcher function so case, function clauses, with-else, and receive
can share one dispatch shape.

## Category

Matcher functions use `FnCategory::Matcher`.

That category means:

- The function is compiler-owned and never appears in source.
- Its name is diagnostic only; callers must use its `FnId`.
- It is a dispatch thunk, not a semantic boundary.
- Reducer/inliner passes may inline it when normal single-use and size rules
  allow it.
- Source reporting should attribute user-facing spans to the original pattern
  or clause, not to the matcher wrapper.

## Internal ABI

A matcher takes only values it needs to route:

```text
matcher(subjects..., success continuations captured as direct FnIds in terms)
```

The first parameters are the matrix subjects in source order. A matcher does
not take user environment captures unless the Decision itself needs them for a
guard or precondition. Leaf bindings are produced inside the matcher by
materializing `SubjectRef` projections:

- `Var(v)` is the original subject parameter.
- `TupleField(base, i)` emits `Prim::TupleField`.
- `ListHead(base)` emits `Prim::ListHead`.
- `ListTail(base)` emits `Prim::ListTail`.

On a successful leaf, the matcher tail-calls the existing leaf continuation
with the same argument order the current in-function path uses:

```text
outer captures..., pattern bindings...
```

On failure, the matcher tail-calls the caller-provided fail continuation or
halts with the same error atom the producer already owns (`:case_clause`,
`:function_clause`, `:with_clause`, or receive miss handling).

## Guards And Preconditions

Preconditions run before guards. Both are rejectable leaf tests:

```text
precondition miss -> reject continuation
guard false       -> reject continuation
guard true        -> leaf continuation
```

This is the same contract as `Decision::Leaf.on_guard_fail`; matcher lowering
must not special-case guards outside the Decision tree.

## Typing

The matcher's return type is the union of the leaf/fail continuation returns
observed through ordinary tail-call edges. It should not introduce a new
typing rule. The typer already understands internal continuation categories;
`FnCategory::Matcher` exists so future category-sensitive passes can identify
the dispatch thunk without name-prefix matching.

## Term::Match

Do not introduce `Term::Match` yet.

The current `Decision` tree already lowers cleanly into ordinary `If`,
`Goto`, and `TailCall` terms. A new terminator would only be worthwhile if the
matcher fn shape proves too noisy for optimization or diagnostics after D2/D3.
Until then, the smaller correct-by-construction move is to reuse existing IR
terms and let the reducer/inliner erase trivial matchers.
