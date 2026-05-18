# apply2 — paper walk

Fixture: `fixtures/apply2/input.fz`. Expected output: `42`, `-7`.

This walkthrough drives every callsite in `main` through the reducer
rules by hand. Same shape as `higher_order` minus `compose`.

## The source

```
fn double(x), do: x * 2
fn neg(x), do: 0 - x
fn apply2(f, x), do: f(x)

fn main() do
  print(apply2(double, 21))
  print(apply2(neg, 7))
end
```

Top-level fn names `double` and `neg` passed as values are sugar for
zero-capture `closure_lit(F, [])` Descrs.

## Call 1 — `apply2(double, 21)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | `apply2` single clause → bind `f := closure_lit(double, [])`, `x := int_lit(21)` | 1 |
| 1.2 | substitute | body `f(x)` → `closure_lit(double, [])(21)` | 1 |
| 1.3 | recurse + closure-inline | callee is a literal closure_lit → reduce `double(21)` (see Findings on closure-inline naming) | 2 |
| 1.3.1 | dispatch | `double` matches → `x := 21` | 2 |
| 1.3.2 | substitute | `x * 2` → `21 * 2` | 2 |
| 1.3.3 | fold-prim | `21 * 2` → `42` | 2 |

**Reduced form:** `42`.

## Call 2 — `apply2(neg, 7)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | `apply2` matches → `f := closure_lit(neg, [])`, `x := 7` | 1 |
| 2.2 | substitute | body → `closure_lit(neg, [])(7)` | 1 |
| 2.3 | recurse + closure-inline | reduce `neg(7)` | 2 |
| 2.3.1 | dispatch | `neg` matches → `x := 7` | 2 |
| 2.3.2 | substitute | `0 - x` → `0 - 7` | 2 |
| 2.3.3 | fold-prim | `0 - 7` → `-7` | 2 |

**Reduced form:** `-7`.

## main, after reduction

```
fn main() do
  print(42)
  print(-7)
end
```

Zero user-fn bodies emitted.

## Structural-decrease check

No recursion. Irrelevant here.

## Findings

**Same payoff and same sub-rule question as `higher_order`.** The
walk is mechanical, but step 1.3 / 2.3 uses
**closure_lit-as-callee dispatch** — the reducer sees a literal
`closure_lit(F, captures)` in callee position and translates the
call to `F(captures ++ args)`. With zero captures this is a no-op
substitution; the dispatch lands on `F` directly.

The seven rules can accommodate this under a broad reading of
`dispatch`, but it's worth naming explicitly. See the `higher_order`
findings for the full discussion.

**No new surprises specific to this fixture.** It's a minimal version
of `higher_order` — useful as a regression target for the
closure-inline rule by itself, without `compose`'s extra layer.

**Predicted shape:** 0 user bodies, 0 allocations.
