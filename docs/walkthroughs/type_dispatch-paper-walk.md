# type_dispatch — paper walk

Ticket family: `fz-RED.*` (paper walks of the proposed compile-time
reducer; this batch focuses on type narrowing & dispatch).

This fixture exercises **typed-clause dispatch**: clause heads carry
a `:: integer` annotation. Under the reducer the head is a type test
on the input Descr. Every step here must be one of the seven named
rules (see `red-0-ast-eval-paper-walk.md`).

## The source

```
fn check(x :: integer) do :is_int end
fn check(x) do :other end

fn main() do
  print(check(42))
  print(check(:foo))
end
```

## Call 1 — `check(42)`

Input Descr: `int_lit(42)` (a literal int).

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | clause 0 head `x :: integer`. Matrix asks: is `int_lit(42) ⊆ integer`? Yes (literal int kind ⊆ integer). Bind `x := 42`. | 1 |
| 1.2 | substitute | body `:is_int` has no free vars; substitution is the identity | 1 |
| 1.3 | fold-prim | result is already a literal atom Descr `:is_int` | 1 |

**Reduced form:** `:is_int`. No residual call.

## Call 2 — `check(:foo)`

Input Descr: `atom_lit(:foo)`.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | clause 0 head `x :: integer`. Matrix asks: is `atom_lit(:foo) ⊆ integer`? No (atom kind disjoint from integer kind). Reject. | 1 |
| 2.2 | dispatch | clause 1 head `x` is untyped — accepts any. Bind `x := :foo`. | 1 |
| 2.3 | substitute | body `:other`; no free vars | 1 |
| 2.4 | fold-prim | result is `:other` literal | 1 |

**Reduced form:** `:other`.

## main, after reduction

```
fn main() do
  print(:is_int)
  print(:other)
end
```

Zero `check` bodies emitted. The TypeTest dissolves entirely — both
inputs are literal Descrs, so dispatch can decide each clause head
statically.

## Findings

The walk is mechanical. The reducer never produced a TypeTest at all
because both inputs were literal Descrs at the callsite — dispatch
folds the type test the same way `fold-prim` folds a known
arithmetic Prim. This is **dispatch eating fold-prim's lunch on
TypeTest-on-literals**, and that's the right thing.

The interesting contrast: if either argument had been opaque
(`check(some_runtime_int)`), dispatch on clause 0 would have asked
"is `T ⊆ integer`?" against an opaque `T`. If `T == integer` ⇒
clause 0 accepts statically; if `T == any` ⇒ neither clause is
statically chosen and the rule fires `stop-opaque`, leaving a real
runtime `TypeTest` in a boundary body for `check`. The existing
fixture doesn't exercise that path — the inputs are too narrow.

No judgment calls surfaced. The seven rules cover this fixture.
