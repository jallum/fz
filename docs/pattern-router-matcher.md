# Pattern Router Matcher

Status: revised by `fz-puj.55`.

The pattern router has one executable matching language:

```text
Matrix -> Matcher -> lowering / receive probing
```

Case, function-clause, and with-else dispatch lower the Matcher graph inline
into the current function. Receive uses the same Matcher representation behind
an ABI-shaped callable boundary because the runtime selective receive loop
needs to probe mailbox messages one at a time.

## Matcher Shape

A Matcher contains only subjects, prepared constants, tests, branches, guards,
bindings, and leaf body ids. It does not carry AST patterns or AST guard
expressions after compilation.

Leaf bindings materialize `SubjectRef` projections:

- `Input(i)` is an original matcher input.
- `TupleField(base, i)` emits tuple projection.
- `ListHead(base)` emits list-head projection.
- `ListTail(base)` emits list-tail projection.

Preconditions lower to explicit `MatcherTest::Type` nodes before guards.
Guard failure and precondition failure both branch to the reject continuation.

## Function Categories

`FnCategory::Matcher` identifies compiler-owned matcher routers. These
functions are dispatch thunks, not user semantic boundaries, and may be
inlined when size and call-convention rules allow it.

`FnCategory::ExternMatcher` identifies the receive ABI form:

```text
fn(msg, pinned, out) -> u32
```

Extern matchers are not IR-inlined because their call convention is part of
the runtime receive contract.
