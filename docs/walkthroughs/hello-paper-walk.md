# hello — paper walk

Drives every top-level callsite in `main` through the seven reducer
rules (see [red-0-ast-eval-paper-walk.md](red-0-ast-eval-paper-walk.md)
for the rule table and the structural-decrease measure).

## The source

```
fn main() do
  print(40 + 2)
  print(:ok)
  print(true)
  print(nil)
end
```

Expected output:
```
42
:ok
true
nil
```

## Call 1 — `print(40 + 2)`

`40 + 2` is a `Prim(add, [int_lit(40), int_lit(2)])` — both inputs
literal Descrs.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | fold-prim | `40 + 2` → `int_lit(42)` | 1 |
| 1.2 | stop-opaque | `print` is an extern/intrinsic — no clauses to dispatch; leave call in place with literal arg | 1 |

**Reduced form:** `print(42)` — one residual call to the print
boundary.

## Call 2 — `print(:ok)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | stop-opaque | arg is already an atom literal Descr; `print` is extern — leave in place | 1 |

**Reduced form:** `print(:ok)`.

## Call 3 — `print(true)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 3.1 | stop-opaque | arg is bool literal Descr; extern callee — leave in place | 1 |

**Reduced form:** `print(true)`.

## Call 4 — `print(nil)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 4.1 | stop-opaque | arg is the `nil` Descr; extern callee — leave in place | 1 |

**Reduced form:** `print(nil)`.

## main, after reduction

```
fn main() do
  print(42)
  print(:ok)
  print(true)
  print(nil)
end
```

The `+` dissolved; all four `print` calls remain.

## Findings

The walk is mechanical. Every step is either `fold-prim` or
`stop-opaque`.

**Expected user-function body count:** 0. `main` is always emitted;
`print` is an extern (not a user fn). No `eval`-style helpers exist.

**Boundary:** `print` is the only boundary, hit four times. It's an
extern/intrinsic — the design doc lists "Extern / FFI call" as a stop
condition. The four `print` calls survive reduction with literal args
(int, atom, bool, nil).

**Feature surfaced — literal Descrs for each scalar shape:** the
reducer needs a literal Descr representation for at least:
- `int_lit(n)`
- `atom_lit(:name)`
- `bool_lit(true|false)`
- `nil` (its own Descr)

These are all in the existing Descr lattice (per `bodies-are-boundaries`
discussion of set-theoretic types), so this is not a gap, just a
checklist item.

**Nothing to call out as a gap.** No patterns, no recursion, no
closures, no macros. The simplest possible fixture for the reducer.
