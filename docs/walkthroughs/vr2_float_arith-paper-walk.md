# vr2_float_arith — paper walk

Drives every top-level callsite in `main` through the seven reducer
rules (see [red-0-ast-eval-paper-walk.md](red-0-ast-eval-paper-walk.md)
for the rule table).

## The source

```
fn main() do
  print(1.5 + 2.5)
  print(10.0 - 3.0)
  print(2.5 * 4.0)
  print(1.0 < 2.0)
end
```

Expected output:
```
4.0
7.0
10.0
true
```

## Call 1 — `print(1.5 + 2.5)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | fold-prim | `1.5 + 2.5` → `float_lit(4.0)` | 1 |
| 1.2 | stop-opaque | `print` extern; leave in place | 1 |

## Call 2 — `print(10.0 - 3.0)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | fold-prim | `10.0 - 3.0` → `float_lit(7.0)` | 1 |
| 2.2 | stop-opaque | `print` extern; leave in place | 1 |

## Call 3 — `print(2.5 * 4.0)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 3.1 | fold-prim | `2.5 * 4.0` → `float_lit(10.0)` | 1 |
| 3.2 | stop-opaque | `print` extern; leave in place | 1 |

## Call 4 — `print(1.0 < 2.0)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 4.1 | fold-prim | `1.0 < 2.0` → `bool_lit(true)` | 1 |
| 4.2 | stop-opaque | `print` extern; leave in place | 1 |

## main, after reduction

```
fn main() do
  print(4.0)
  print(7.0)
  print(10.0)
  print(true)
end
```

## Findings

The walk is mechanical.

**Expected user-function body count:** 0. No user functions defined.
`main` is always emitted; `print` is extern.

**Boundaries:** only `print` (four times).

**Feature surfaced — `fold-prim` must cover float arithmetic AND
comparison-returning-bool.**
- `float + float`, `float - float`, `float * float` → `float_lit`.
- `float < float` → `bool_lit`.

Both kinds are within `fold-prim`'s purview (literal-input Prims),
but the comparison case is the first one in this batch where the
output Descr kind differs from the input. The implementation must
not assume "Prim output kind = Prim input kind."

**Feature surfaced — float-precision question.** `1.5 + 2.5 = 4.0`
exactly in f64; `2.5 * 4.0 = 10.0` exactly. None of the operations
in this fixture surface rounding behavior. *If* a future fixture
folds e.g. `0.1 + 0.2`, the reducer must compute with the same f64
semantics as the runtime to preserve three-path parity. **Not a gap
here, but a precondition to record:** `fold-prim`'s arithmetic for
floats must use the same IEEE-754 semantics codegen emits.

**Nothing to call out as a gap for this fixture.**
