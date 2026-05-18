# fib_tailrec — paper walk

Fixture: `fixtures/fib_tailrec/input.fz`. Expected stdout:

```
0
1
55
6765
```

This fixture exercises **three-clause dispatch on a 3-arg function**
with literal-int countdown in the first slot and pure arithmetic on
the accumulator slots. The largest input (`fib(20, 0, 1)`) takes 20
steps — still under the 32-step budget — so we expect all four calls
to reduce to constants.

## Source

```
fn fib(0, a, _), do: a
fn fib(1, _, b), do: b
fn fib(n, a, b), do: fib(n - 1, b, a + b)

fn main() do
  print(fib(0, 0, 1))
  print(fib(1, 0, 1))
  print(fib(10, 0, 1))
  print(fib(20, 0, 1))
end
```

## Call 1 — `fib(0, 0, 1)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | input `(0, 0, 1)`; clause 0 head `(0, a, _)` matches → bind `a := 0` (`_` no binding) | 1 |
| 1.2 | substitute | body → `0` | 1 |

**Reduced form:** `0`.

## Call 2 — `fib(1, 0, 1)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | clause 0 rejects (slot 0 `1 ≠ 0`); clause 1 head `(1, _, b)` matches → bind `b := 1` | 1 |
| 2.2 | substitute | body → `1` | 1 |

**Reduced form:** `1`.

## Call 3 — `fib(10, 0, 1)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 3.1 | dispatch | clauses 0,1 reject; clause 2 matches → `n := 10`, `a := 0`, `b := 1` | 1 |
| 3.2 | substitute | → `fib(10 - 1, 1, 0 + 1)` | 1 |
| 3.3 | fold-prim | → `fib(9, 1, 1)` | 1 |
| 3.4 | recurse | literal `9 < 10` ✓ | 2 |
| 3.4.* | (same shape) | → `fib(8, 1, 2)` → `fib(7, 2, 3)` → `fib(6, 3, 5)` → `fib(5, 5, 8)` → `fib(4, 8, 13)` → `fib(3, 13, 21)` → `fib(2, 21, 34)` → `fib(1, 34, 55)` | 3..10 |
| 3.5 | dispatch | `fib(1, 34, 55)` matches clause 1 → `b := 55` | 10 |
| 3.6 | substitute | → `55` | 10 |
| → all returns propagate | | up through 10 frames, each is just the inner literal | 10 |

**Reduced form:** `55`. Counter peaked at 10.

## Call 4 — `fib(20, 0, 1)`

Same shape as Call 3, just twice as deep. Counter peaks around 20
(still under 32).

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 4.1 | dispatch | clause 2 matches → `n := 20`, `a := 0`, `b := 1` | 1 |
| 4.2 | substitute + fold-prim | → `fib(19, 1, 1)` | 1 |
| 4.3 | recurse | `19 < 20` ✓ | 2 |
| 4.3.* | (same shape, 18 more steps) | → `fib(18, 1, 2)` → `fib(17, 2, 3)` → ... → `fib(1, 4181, 6765)` | 3..20 |
| 4.4 | dispatch | `fib(1, 4181, 6765)` matches clause 1 → `b := 6765` | 20 |
| 4.5 | substitute | → `6765` | 20 |

**Reduced form:** `6765`. Counter peaked at 20.

## main, after reduction

```
fn main() do
  print(0); print(1); print(55); print(6765)
end
```

Zero `fib` bodies.

## Findings

**Three-arg dispatch is the same matrix shape, wider.** Clause heads
are 3-tuples of patterns; dispatch tries each clause's full row
against the input row. No new rule needed.

**Decrease check applies to a single slot.** `fib(n, a, b) → fib(n -
1, b, a + b)` — the *first* argument decreases (literal `n - 1`
strictly less than literal `n`), while `a` and `b` grow. The
structural-decrease check needs to recognize that *any* argument
slot's strict decrease is sufficient.

**Recommendation:** the rule should be "at least one argument
slot is provably structurally smaller, and no slot grows in a way that
threatens termination." For `fib`, slot 0 shrinks; slots 1 and 2 are
unbounded but irrelevant to termination (they're accumulators). The
matrix only dispatches on slot 0 (the literal-int clauses use `_` for
slots 1 and 2), so the matrix structure makes slot 0 the decisive
slot.

This is a subtle point — the *general* structural-decrease check
requires a per-callee analysis of which argument slots matter for
termination. In practice, "any slot strictly smaller and no slot is
opaque-incremented" is a sound conservative rule. Worth surfacing as
a design point.

**Counter scaling with literal input.** `fib(20, ...)` peaks at 20.
For `fib(31, ...)` we'd peak at 31 and still commit. `fib(32, ...)`
would land exactly at 32 and either commit or trip `stop-budget`
depending on how `≤ 32` vs `< 33` is interpreted. `fib(33, ...)`
would definitely trip `stop-budget` — and per the all-or-nothing
rule, the entire reduction is discarded and `fib` ships as a body
called with the literal `(33, 0, 1)` argument.

This is the "almost fits in budget" surprise the design discussion
already flagged (Issue 3): the user gets a body call for `fib(33,
0, 1)` even though it would unroll in 33 steps. The `--explain-bodies`
diagnostic (RED.7) is how the user discovers and tunes around this.

**Tail-call shape is irrelevant to the reducer.** `fib`'s recursive
call is in tail position; the source-level distinction between
`Call` and `TailCall` is a codegen concern. The reducer just sees a
call with literal arguments and recurses on it.

**Bodies emitted by main:** **zero**.
</content>
</invoke>