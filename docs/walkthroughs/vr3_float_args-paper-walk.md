# vr3_float_args — paper walk

Drives every top-level callsite in `main` through the seven reducer
rules (see [red-0-ast-eval-paper-walk.md](red-0-ast-eval-paper-walk.md)
for the rule table).

This fixture is structurally **identical** to
[vr3_int_args](vr3_int_args-paper-walk.md) — a single-clause
arithmetic helper called once from `main` with all-literal args. The
only differences are: two params instead of three, float literals
instead of int, an `x*x + y*y` expression instead of `a + b + c`.

## The source

```
fn dist(x, y) do
  x * x + y * y
end

fn main() do
  print(dist(1.5, 2.5))
end
```

Expected output: `8.5`.

## Call 1 — `print(dist(1.5, 2.5))`

### Inner — `dist(1.5, 2.5)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | sole clause head `(x, y)` matches; bind `x := 1.5`, `y := 2.5` | 1 |
| 1.2 | substitute | body `x * x + y * y` → `1.5 * 1.5 + 2.5 * 2.5` | 1 |
| 1.3 | fold-prim | `1.5 * 1.5` → `float_lit(2.25)` | 2 |
| 1.4 | fold-prim | `2.5 * 2.5` → `float_lit(6.25)` | 3 |
| 1.5 | fold-prim | `2.25 + 6.25` → `float_lit(8.5)` | 4 |

Inner result: `float_lit(8.5)`.

### Outer — `print(8.5)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.6 | stop-opaque | `print` extern; leave in place | 4 |

## main, after reduction

```
fn main() do
  print(8.5)
end
```

## Findings

The walk is mechanical. Same shape as `vr3_int_args`; refer to that
walk for the design discussion.

**Expected user-function body count:** 0.

**Boundaries:** only `print`.

**Feature surfaced (in addition to vr3_int_args):** the same
parameter occurs more than once in the body (`x * x`, `y * y`).
`substitute` replaces *every* occurrence of the bound name with its
Descr — this is standard capture-avoiding substitution. Worth being
explicit: `substitute` is multi-occurrence, not single-use.

**Reuses the float-precision precondition from
[vr2_float_arith](vr2_float_arith-paper-walk.md):** `fold-prim` must
match IEEE-754 codegen semantics. `1.5 * 1.5 = 2.25` exactly,
`2.25 + 6.25 = 8.5` exactly, so this fixture surfaces no rounding.

**Nothing to call out as a gap.**
