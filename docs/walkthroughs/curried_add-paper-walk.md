# curried_add — paper walk

Fixture: `fixtures/curried_add/input.fz`. Expected output: `42`, `6`.

This walkthrough drives every `apply(...)` chain in `main` through
the reducer rules by hand. This is **three-level currying**: each
outer call produces a closure_lit; each `apply` unwraps one level.
The challenge is whether the reducer cleanly threads through three
nested closure_lit literals.

## The source

```
fn add3(x), do: fn(y) -> fn(z) -> x + y + z
fn apply(f, x), do: f(x)

fn main() do
  print(apply(apply(add3(10), 20), 12))
  print(apply(apply(add3(1), 2), 3))
end
```

Naming:

- `L1` = `fn(y) -> fn(z) -> x + y + z`; param `y`; captures `[x]`.
- `L2` = `fn(z) -> x + y + z`; param `z`; captures `[x, y]`.

So `add3(x)` returns `closure_lit(L1, [x])`. Applying it to `y`
produces (via L1's body) `closure_lit(L2, [x, y])`. Applying that to
`z` reduces to `x + y + z`.

## Call 1 — `apply(apply(add3(10), 20), 12)`

Innermost-first reduction.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | `add3(10)`: single clause → bind `x := 10` | 1 |
| 1.2 | substitute | body `fn(y) -> ...` → `MakeClosure(L1, [10])` | 1 |
| 1.3 | fold-prim | `MakeClosure(L1, [10])` → `closure_lit(L1, [10])` | 1 |
| → | | innermost arg is now `closure_lit(L1, [10])` | |
| 1.4 | dispatch | outer `apply(closure_lit(L1, [10]), 20)`: bind `f := closure_lit(L1, [10])`, `x := 20` | 2 |
| 1.5 | substitute | body `f(x)` → `closure_lit(L1, [10])(20)` | 2 |
| 1.6 | closure-inline | callee is literal closure_lit → translate to `L1(10, 20)` (captures preconcat'd) | 3 |
| 1.7 | dispatch | `L1` single clause; binders `x` (capture), `y` (param) → bind `x := 10`, `y := 20` | 3 |
| 1.8 | substitute | body `fn(z) -> x + y + z` → `MakeClosure(L2, [10, 20])` | 3 |
| 1.9 | fold-prim | → `closure_lit(L2, [10, 20])` | 3 |
| → | | middle apply has reduced to a literal closure_lit | |
| 1.10 | dispatch | outermost `apply(closure_lit(L2, [10, 20]), 12)`: bind `f := closure_lit(L2, [10, 20])`, `x := 12` | 4 |
| 1.11 | substitute | body `f(x)` → `closure_lit(L2, [10, 20])(12)` | 4 |
| 1.12 | closure-inline | → translate to `L2(10, 20, 12)` | 5 |
| 1.13 | dispatch | `L2` single clause; binders `x, y` (captures), `z` (param) → bind `x := 10`, `y := 20`, `z := 12` | 5 |
| 1.14 | substitute | body `x + y + z` → `10 + 20 + 12` | 5 |
| 1.15 | fold-prim | → `42` | 5 |

**Reduced form:** `42`. Counter peaked at 5.

## Call 2 — `apply(apply(add3(1), 2), 3)`

Same shape as Call 1 with different literals.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | `add3(1)` → `x := 1` | 1 |
| 2.2 | substitute + fold-prim | → `closure_lit(L1, [1])` | 1 |
| 2.3 | dispatch + substitute | middle `apply` → `closure_lit(L1, [1])(2)` | 2 |
| 2.4 | closure-inline + dispatch | `L1(1, 2)` → bind `x := 1`, `y := 2` | 3 |
| 2.5 | substitute + fold-prim | body → `closure_lit(L2, [1, 2])` | 3 |
| 2.6 | dispatch + substitute | outer `apply` → `closure_lit(L2, [1, 2])(3)` | 4 |
| 2.7 | closure-inline + dispatch | `L2(1, 2, 3)` → bind `x := 1, y := 2, z := 3` | 5 |
| 2.8 | substitute + fold-prim | `1 + 2 + 3` → `6` | 5 |

**Reduced form:** `6`.

## main, after reduction

```
fn main() do
  print(42)
  print(6)
end
```

Zero user-fn bodies emitted. The three nested layers of currying
each produced a literal `closure_lit` Descr that got consumed by the
next `apply`'s closure-inline step, then dissolved into substitute.
No closure heap objects are allocated at runtime.

## Structural-decrease check

No recursive calls. The walk is purely inline-and-fold over a
fixed-depth tower of closure_lit literals.

## Findings

**The walk is mechanical end-to-end** — using the same closure-inline
sub-rule introduced in the higher-order fixtures.

**The repeated pattern.** Each `apply` in the chain follows the same
shape:

1. The outer `apply` clause binds `f` to a literal `closure_lit`.
2. `substitute` puts the closure_lit in callee position.
3. **closure-inline** translates `closure_lit(F, captures)(arg)` to
   `F(captures ++ [arg])`.
4. `dispatch` selects F's clause and binds captures + args together.
5. F's body either produces another `MakeClosure` (fold-prim → next
   closure_lit literal) or arithmetic (fold-prim → scalar literal).

**Iterating closure_lit Descrs through fold-prim.** The fact that
`MakeClosure([literal captures])` folds to a literal `closure_lit`
Descr is what lets this terminate. If the type lattice did *not*
admit closure_lit as a literal output of fold-prim, the middle
`apply`'s argument would be opaque and reduction would stop there.
**This is a load-bearing property** for currying: the design needs
to commit to "closure_lit with all-literal captures *is* a literal
Descr that fold-prim emits."

**Three-level (or N-level) currying generalizes.** Each level adds 2-
3 counter ticks. A 32-level curry stays well under budget.

**Predicted shape:** 0 user bodies, 0 allocations. Matches the
design-doc table.
