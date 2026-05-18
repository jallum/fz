# vr3_int_args — paper walk

Drives every top-level callsite in `main` through the seven reducer
rules (see [red-0-ast-eval-paper-walk.md](red-0-ast-eval-paper-walk.md)
for the rule table).

## The source

```
fn sum3(a, b, c) do
  a + b + c
end

fn main() do
  print(sum3(40, 1, 1))
end
```

Expected output: `42`.

## Call 1 — `print(sum3(40, 1, 1))`

Descend into the inner `sum3` call first.

### Inner — `sum3(40, 1, 1)`

`sum3/3` is a single-clause function with three plain-variable
parameters.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | sole clause head `(a, b, c)` matches; bind `a := 40`, `b := 1`, `c := 1` | 1 |
| 1.2 | substitute | body `a + b + c` → `40 + 1 + 1` | 1 |
| 1.3 | fold-prim | left-assoc: inner `40 + 1` → `int_lit(41)` | 2 |
| 1.4 | fold-prim | outer `41 + 1` → `int_lit(42)` | 3 |

Inner result: `int_lit(42)`.

### Outer — `print(42)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.5 | stop-opaque | `print` extern; leave in place | 3 |

**Reduced form:** `print(42)`.

## main, after reduction

```
fn main() do
  print(42)
end
```

`sum3` dissolves completely.

## Findings

The walk is mechanical.

**Expected user-function body count:** 0. `sum3`'s sole callsite has
all-literal args, so the reducer fully consumes it. `main` is always
emitted; `print` is extern.

**Boundaries:** only `print`.

**Feature surfaced — multi-parameter dispatch on plain-variable
heads.** Pattern matrix must bind `(a, b, c)` to a 3-tuple of input
Descrs. Trivial case; no destructuring.

**Feature surfaced — left-associative chained Prims.** `a + b + c` is
`Prim(add, [Prim(add, [a, b]), c])`. The inner Prim folds before the
outer; this is exactly the existing `ir_fold` block-level behavior
and falls out of `fold-prim` natural traversal.

**Tangential observation (cf. the fixture's README).** The README
describes downstream wins: typed ABI (`tail` calling convention,
block-param i64s, no entry frame, no `fz_alloc_frame`). All of those
become moot in the reduced program — there are zero `sum3` calls
left at runtime. The reducer's job here makes the README's wins
unnecessary for *this* fixture; the same wins still matter for any
fixture where `sum3` (or similar) survives reduction (opaque-int
callers).

**Nothing to call out as a gap.**
