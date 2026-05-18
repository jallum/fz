# add1 — paper walk

Drives every top-level callsite in `main` through the seven reducer
rules (see [red-0-ast-eval-paper-walk.md](red-0-ast-eval-paper-walk.md)
for the rule table).

## The source

```
fn add1(n) do n + 1 end

fn main() do
  print(add1(41))
end
```

Expected output: `42`.

## Call 1 — `print(add1(41))`

The outer call is `print(...)`; its argument is `add1(41)`. The
reducer descends outside-in: dispatch the inner call first because its
result becomes a literal Descr the outer call needs.

### Inner — `add1(41)`

`add1/1` is a single-clause function with a plain-variable pattern
head `(n)` — any input matches; bind `n := the_input`.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | sole clause head `(n)` matches `int_lit(41)`; bind `n := 41` | 1 |
| 1.2 | substitute | body `n + 1` → `41 + 1` | 1 |
| 1.3 | fold-prim | `41 + 1` → `int_lit(42)` | 1 |

Inner result: `int_lit(42)`. The `add1` body is no longer referenced
from `main`.

### Outer — `print(42)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.4 | stop-opaque | `print` is extern; leave in place with literal arg | 1 |

## main, after reduction

```
fn main() do
  print(42)
end
```

`add1` dissolved completely.

## Findings

The walk is mechanical. Three rules fire: `dispatch` (trivial — single
clause, single var binding), `substitute`, `fold-prim`.

**Expected user-function body count:** 0. `add1` is fully reducible
from its sole callsite. `main` is always emitted; `print` is extern.

**Boundary:** only `print`. One residual call.

**Nothing to call out as a gap.** This fixture is the minimum
non-trivial reducer case: one user function, one callsite, literal
input. The "dispatch on a plain-variable head matches anything"
behavior is the trivial dispatch case the pattern matrix
(fz-ul4.43) must handle.
