# polymorphic — paper walk

Fixture: `fixtures/polymorphic/input.fz`. Expected output: `42`,
`:hello`, `true`.

This walkthrough drives every `id(...)` callsite in `main` through
the reducer rules **by hand**. The spike succeeds iff every step is
mechanical — one of the named rules — and we land at the correct
values.

## The source

```
fn id(x), do: x

fn main() do
  print(id(42))
  print(id(:hello))
  print(id(true))
end
```

A single-clause function whose body is the bound name itself. There
is nothing to fold, no recursion, no closure_lit — just dispatch +
substitute.

## Call 1 — `id(42)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | one clause; head `x` is a bare binder, always matches → bind `x := int_lit(42)` | 1 |
| 1.2 | substitute | body `x` → `42` | 1 |

**Reduced form:** `42` (literal). No call to `id` remains.

## Call 2 — `id(:hello)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | head `x` matches → bind `x := atom_lit(:hello)` | 1 |
| 2.2 | substitute | body `x` → `:hello` | 1 |

**Reduced form:** `:hello`.

## Call 3 — `id(true)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 3.1 | dispatch | head `x` matches → bind `x := bool_lit(true)` | 1 |
| 3.2 | substitute | body `x` → `true` | 1 |

**Reduced form:** `true`.

## main, after reduction

```
fn main() do
  print(42)
  print(:hello)
  print(true)
end
```

The three `id(...)` calls dissolved entirely. Zero `id` bodies are
forced into existence by main. The compiled binary contains only
`main`, the three `print` calls, and runtime shims.

## Structural-decrease check

No recursion. The recurse rule never fires; `stop-non-decrease` and
`stop-budget` are irrelevant.

## Findings

**The walk is mechanical end-to-end.** Two rules carry it: `dispatch`
(against a single bare-binder pattern, which is trivially total) and
`substitute`. Every step in every call above is one of the seven
named rules.

**The polymorphism point.** Each callsite presents a different input
Descr (`int_lit`, `atom_lit`, `bool_lit`). The reducer never has to
choose a single type for `id`; it reduces three separate callsites
independently. No `id` body needs to exist — the polymorphism
dissolves at compile time. This is the contract the design promises:
"functions are templates, not specs."

**No closure_lit involved.** `id` is referenced by name only in
direct call position, not passed as a value. The interesting
closure-reduction work shows up in `higher_order`, `apply2`, and the
list-with-fn-arg fixtures.

**No surprises.** The seven rules cover this fixture cleanly.

**Predicted shape:** 0 user bodies, 0 allocations. Matches the
design-doc table.
