# Pattern Router Dispatch ABI

Status: revised by `fz-puj.52.7`.

The pattern router now has one source of truth:

```text
Matrix -> Decision -> lowering
```

Case, function-clause, and with-else dispatch lower the Decision tree directly
into the current function. That keeps internal compiler dispatch out of the
ordinary function/spec surface: the typer sees the user function and its clause
continuations, not a second set of spec-producing matcher wrappers.

Receive remains the ABI-driven matcher-function case because the runtime
selective receive loop needs a callable predicate/continuation boundary while
probing mailbox messages.

## Category

Callable matcher functions use `FnCategory::Matcher`.

That category means:

- The function is compiler-owned and never appears in source.
- Its name is diagnostic only; callers must use its `FnId`.
- It is a dispatch thunk, not a semantic boundary.
- Reducer/inliner passes may inline the matcher shell when normal single-use
  and size rules allow it, but must not inline leaf bodies into the matcher
  before that decision. Matcher inlining stops at the successful/failing
  dispatch point.
- Source reporting should attribute user-facing spans to the original pattern
  or clause, not to the matcher wrapper.

Internal case/function/with dispatch should not mint `FnCategory::Matcher`
functions in production lowering.

## Internal ABI

A callable matcher takes only values it needs to route:

```text
matcher(subjects..., success continuations captured as direct FnIds in terms)
```

The first parameters are the matrix subjects in source order. A callable
matcher does not take user environment captures unless the Decision itself
needs them for a guard or precondition. Leaf bindings are produced inside the
matcher by materializing `SubjectRef` projections:

- `Var(v)` is the original subject parameter.
- `TupleField(base, i)` emits `Prim::TupleField`.
- `ListHead(base)` emits `Prim::ListHead`.
- `ListTail(base)` emits `Prim::ListTail`.

On a successful leaf, the callable matcher tail-calls the existing leaf
continuation with the same argument order the in-function path uses:

```text
outer captures..., pattern bindings...
```

On failure, the callable matcher tail-calls the caller-provided fail
continuation or halts with the same error atom the producer already owns
(`:case_clause`, `:function_clause`, `:with_clause`, or receive miss handling).

## Guards And Preconditions

Preconditions run before guards. Both are rejectable leaf tests:

```text
precondition miss -> reject continuation
guard false       -> reject continuation
guard true        -> leaf continuation
```

This is the same contract as `Decision::Leaf.on_guard_fail`; lowering must not
special-case guards outside the Decision tree.

## Typing

Inline dispatch has the return type of its enclosing function. A callable
matcher's return type is the union of the leaf/fail continuation returns
observed through ordinary tail-call edges. It should not introduce a new typing
rule. The typer already understands internal continuation categories;
`FnCategory::Matcher` exists so category-sensitive passes can identify the
dispatch thunk without name-prefix matching.

## Term::Match

Do not introduce `Term::Match` yet.

The current `Decision` tree already lowers cleanly into ordinary `If`,
`Goto`, and `TailCall` terms. The matcher-fn shape proved too noisy for
internal dispatch because it duplicated spec-producing function entries. The
smaller correct-by-construction move is to reuse existing IR terms inline, and
reserve callable matchers for runtime boundaries such as receive.
