# nested_modules — paper walk under the RED.0 reducer

Paper-only walk through every callsite in `main` and every internal
call exposed by reduction. Rules: see `red-0-ast-eval-paper-walk.md`.

Expected output: `7`, `1007`, `1007`.

## The source

```
defmodule Outer do
  fn f(x), do: x

  defmodule Inner do
    fn f(x), do: x + 1000
  end

  fn use_inner(x), do: Inner.f(x)
end

fn main() do
  print(Outer.f(7))
  print(Outer.Inner.f(7))
  print(Outer.use_inner(7))
end
```

Module structure: `Outer` contains `Inner`. Two fns named `f` exist
under different fully-qualified names: `Outer.f` and `Outer.Inner.f`.
Inside `Outer`, the unqualified name `Inner.f` refers to
`Outer.Inner.f` (sibling-module short-form addressing). After name
resolution every call in the IR carries a fully-qualified `FnId`; the
reducer sees three distinct fns plus `main`. Name resolution is a
front-end concern.

## Call 1 — `Outer.f(7)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | single clause `f(x)` → `x := 7` | 1 |
| 1.2 | substitute | body `x` → `7` | 1 |
| 1.3 | fold-prim | already a literal; nothing to fold | 1 |

**Reduced form:** `7` (literal).

## Call 2 — `Outer.Inner.f(7)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | single clause `f(x)` (the Inner one) → `x := 7` | 1 |
| 2.2 | substitute | body `x + 1000` → `7 + 1000` | 1 |
| 2.3 | fold-prim | `7 + 1000` → `1007` | 1 |

**Reduced form:** `1007` (literal).

The fact that the callee is at depth 2 in the module tree
(`Outer.Inner`) has no effect on the reducer. The FnId is a flat
symbol by reducer time.

## Call 3 — `Outer.use_inner(7)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 3.1 | dispatch | single clause `use_inner(x)` → `x := 7` | 1 |
| 3.2 | substitute | body `Inner.f(x)` → `Inner.f(7)` (resolved to `Outer.Inner.f(7)` by parser/lowering) | 1 |
| 3.3 | recurse | reduce `Outer.Inner.f(7)` — same shape as Call 2 | 2 |
| 3.3.1 | dispatch | clause `f(x)` → `x := 7` | 2 |
| 3.3.2 | substitute | `x + 1000` → `7 + 1000` | 2 |
| 3.3.3 | fold-prim | → `1007` | 2 |

**Reduced form:** `1007` (literal). Counter 2.

## main, after reduction

```
fn main() do
  print(7)
  print(1007)
  print(1007)
end
```

**Zero bodies** emitted for `Outer.f`, `Outer.Inner.f`,
`Outer.use_inner`. All three calls dissolve to literals.

## Findings

**Nested modules behave exactly like flat modules at reducer time.**
The reducer never sees the nesting; it sees three fully-qualified
FnIds. The Inner-vs-Outer disambiguation happened during parsing /
lowering. This confirms the "modules are namespacing only" hypothesis.

**Short-form addressing (`Inner.f` inside `Outer`) is a front-end
concern.** By the time the reducer runs, `Inner.f` inside
`Outer.use_inner`'s body is already an IR `Call` node whose callee is
the fully-qualified `Outer.Inner.f`. The reducer doesn't need to
implement any lexical-scope lookup; the symbol is already resolved.
Same conclusion as the `modules` fixture: **the reducer rules need no
extension for nesting.**

**Two fns named `f` is not a name clash for the reducer.** Different
FnIds. Dispatch is per-FnId. No new rule.

**Predicted shape:** 0 user bodies, 0 allocations. Matches the
`bodies-are-boundaries.md` table pattern for fully-reduced fixtures.

**Spike outcome for this fixture: GO.** No hopeless issue. The seven
rules suffice.
