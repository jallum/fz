# multi_clause — paper walk

Fixture: `fixtures/multi_clause/input.fz`. Expected stdout:

```
:zero
:positive
:negative
120
```

This fixture exercises **multi-clause dispatch with a guard clause**
(`when n > 0`) and **recursive `fact`** with literal-int decrement.

## Source

```
fn classify(0), do: :zero
fn classify(n) when n > 0, do: :positive
fn classify(_), do: :negative

fn fact(0), do: 1
fn fact(n), do: n * fact(n - 1)

fn main() do
  print(classify(0))
  print(classify(7))
  print(classify(-3))
  print(fact(5))
end
```

## Call 1 — `classify(0)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | clause 0 head `0` matches literal `0` → no bindings | 1 |
| 1.2 | substitute | body is the atom literal `:zero` — nothing to substitute | 1 |

**Reduced form:** `:zero` (literal atom). No call to `classify` remains.

## Call 2 — `classify(7)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | clause 0 rejects (`7 ≠ 0`); clause 1 head `n` + guard `n > 0` — bind `n := 7`, then test guard: `7 > 0` literal-folds to `true` → guard passes | 1 |
| 2.2 | substitute | body → `:positive` | 1 |

**Reduced form:** `:positive`. No residual call.

## Call 3 — `classify(-3)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 3.1 | dispatch | clause 0 rejects (`-3 ≠ 0`); clause 1 binds `n := -3` and tests guard `-3 > 0` → literal-folds to `false` → **clause 1 rejects**; clause 2 head `_` matches → no bindings | 1 |
| 3.2 | substitute | body → `:negative` | 1 |

**Reduced form:** `:negative`. No residual call.

## Call 4 — `fact(5)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 4.1 | dispatch | clause 0 rejects (`5 ≠ 0`); clause 1 matches → `n := 5` | 1 |
| 4.2 | substitute | body → `5 * fact(5 - 1)` | 1 |
| 4.3 | fold-prim | `5 - 1` → `4`; body now `5 * fact(4)` | 1 |
| 4.4 | recurse | `fact(4)` — literal `4 < 5` ✓ | 2 |
| 4.4.1 | dispatch | clause 1 matches → `n := 4` | 2 |
| 4.4.2 | substitute + fold-prim | → `4 * fact(3)` | 2 |
| 4.4.3 | recurse | `fact(3)` literal `3 < 4` ✓ | 3 |
| 4.4.3.* | (same shape) | → `3 * fact(2)` → `3 * (2 * fact(1))` → ... | 4 |
| 4.4.4 | recurse | `fact(2)` → `2 * fact(1)` | 5 |
| 4.4.5 | recurse | `fact(1)` → `1 * fact(0)` | 6 |
| 4.4.6 | recurse | `fact(0)` — clause 0 matches → `1` | 7 |
| 4.4.7 | fold-prim | `1 * 1` → `1` | 7 |
| 4.4.8 | fold-prim | `2 * 1` → `2` | 7 |
| 4.4.9 | fold-prim | `3 * 2` → `6` | 7 |
| 4.4.10 | fold-prim | `4 * 6` → `24` | 7 |
| 4.5 | fold-prim | `5 * 24` → `120` | 7 |

**Reduced form:** `120`. Counter peaked at 7 — well under budget (32).

## main, after reduction

```
fn main() do
  print(:zero)
  print(:positive)
  print(:negative)
  print(120)
end
```

Zero `classify` bodies. Zero `fact` bodies.

## Findings

**Guard clauses introduce a new wrinkle.** The seven rules name
*pattern* matching for dispatch, but `classify`'s clause 1 also has a
**guard**: `when n > 0`. Calls 2 and 3 require the reducer to *evaluate
the guard at compile time* and use the result to accept or reject the
clause. Mechanically this is `dispatch` followed by an implicit
`fold-prim` on the guard expression — but the seven rules as stated
don't explicitly cover the guard step.

**Recommendation:** either extend `dispatch` to "match pattern *and*
prove guard true with current bindings" (treating a guard that
fold-prims to `false` as a clause rejection), or add an 8th rule
`dispatch-guard` for the guard fold. The natural framing is the
former — guards are part of clause-head matching, same as patterns.
This needs explicit naming somewhere in the reducer spec.

**Open question on opaque inputs to guarded clauses.** If `classify`
were called with an *opaque* `int`, dispatch would have to give up
on the guarded clause (can't prove `n > 0` either way). That's
**stop-opaque** behavior — but it would also force `classify` to ship
a body that evaluates the guard at runtime. The pattern matrix
(fz-ul4.43) presumably already handles this, but the reducer-side
contract needs to say so.

**Literal-int recursion reduces as expected.** `fact(5)` unrolls in 7
steps; structural decrease at each `fact(n - 1)` site holds because
`n` is a literal at every level (5, 4, 3, 2, 1, 0). This matches the
bodies-are-boundaries claim: literal-int decrement qualifies as
decrease.

**Bodies emitted by main:** **zero**. Every call dissolves.
</content>
</invoke>