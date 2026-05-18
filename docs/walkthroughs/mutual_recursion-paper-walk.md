# mutual_recursion — paper walk

Fixture: `fixtures/mutual_recursion/input.fz`. Expected stdout:

```
true
true
true
true
```

This fixture exercises **mutual recursion** with literal-int countdown
across two functions. The bodies-are-boundaries design note flagged
this as the case where "literal int countdown reduces, opaque int
decrement doesn't" — we walk the literal-int case and confirm it
unrolls fully.

## Source

```
fn is_even(0), do: true
fn is_even(n), do: is_odd(n - 1)
fn is_odd(0), do: false
fn is_odd(n), do: is_even(n - 1)

fn main() do
  print(is_even(10))
  print(is_odd(7))
  print(is_even(0))
  print(is_odd(1))
end
```

## Call 1 — `is_even(10)`

Walking steps 1, 2, 3, then jumping to the final step:

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | clause 0 rejects (`10 ≠ 0`); clause 1 matches → `n := 10` | 1 |
| 1.2 | substitute | body → `is_odd(10 - 1)` | 1 |
| 1.3 | fold-prim | → `is_odd(9)` | 1 |
| 1.4 | recurse | literal `9 < 10` ✓ (cross-callee; smaller-than-parent's-input holds) | 2 |
| 1.4.1 | dispatch (`is_odd`) | clause 0 rejects (`9 ≠ 0`); clause 1 matches → `n := 9` | 2 |
| 1.4.2 | substitute + fold-prim | → `is_even(8)` | 2 |
| 1.4.3 | recurse | `8 < 9` ✓ | 3 |
| 1.4.3.* | (same shape) | → `is_odd(7)` → `is_even(6)` → ... | 3..9 |
| ... | ... | ... | ... |
| 1.*.final-1 | recurse | `is_even(0)` | 10 |
| 1.*.final | dispatch | `is_even(0)` clause 0 head `0` matches → no bindings | 10 |
| 1.*.final+1 | substitute | body → `true` | 10 |
| → all returns propagate | fold | each `is_odd(0)`/`is_even(0)` site folds to its literal; chain dissolves | 10 |

**Reduced form:** `true`. Counter peaked around 10 — comfortably under
budget (32).

## Call 2 — `is_odd(7)`

Symmetric to Call 1; 7 steps of countdown ending at `is_odd(7) →
is_even(6) → ... → is_odd(1) → is_even(0) → true`.

Wait — the final step: `is_odd(1) → is_even(0)`. `is_even(0)` matches
clause 0 → `true`. So `is_odd(1)` reduces to `true` ✓ (odd number is
odd). **Reduced form:** `true`. Counter peaked ~7.

## Call 3 — `is_even(0)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 3.1 | dispatch | clause 0 head `0` matches → no bindings | 1 |
| 3.2 | substitute | body → `true` | 1 |

**Reduced form:** `true`. Single step.

## Call 4 — `is_odd(1)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 4.1 | dispatch | clause 0 rejects (`1 ≠ 0`); clause 1 matches → `n := 1` | 1 |
| 4.2 | substitute + fold-prim | → `is_even(0)` | 1 |
| 4.3 | recurse | `0 < 1` ✓ | 2 |
| 4.3.1 | dispatch | clause 0 matches → no bindings | 2 |
| 4.3.2 | substitute | → `true` | 2 |

**Reduced form:** `true`.

## main, after reduction

```
fn main() do
  print(true); print(true); print(true); print(true)
end
```

Zero `is_even` bodies. Zero `is_odd` bodies.

## Findings

**Cross-callee structural decrease is the same check as same-callee.**
When `is_even(10)` calls `is_odd(9)`, the recurse rule needs to
confirm that `9` is strictly smaller than `10` in some structural
measure. For literal ints, this is just numeric comparison on the
literal Descrs.

The seven-rule spec says structural decrease is "a sub-Descr extracted
by projection (tuple field, list head/tail, pattern binding) of D".
Literal-int decrement (`n - 1` where `n` is a literal) doesn't fit
that exact wording — it's an *arithmetic* decrease, not a projection.

**Recommendation:** the rule's wording should explicitly admit
"literal-int after constant-folding is smaller than the literal-int
it derives from." The spike walkthrough (ast_eval) and
bodies-are-boundaries both rely on this; it's already implicit but
should be stated.

Concretely: structural-decrease admits:
- *Sub-Descr extraction* (projection): tuple field, list head/tail,
  pattern binding.
- *Literal-int arithmetic*: any literal int produced by fold-prim
  whose value is strictly less than the parent's input literal.

The second is what makes `mutual_recursion(10)` and `fib_tailrec` and
`fact` all reduce. The first is what makes `ast_eval` reduce.

**Mutual recursion needs a "shared budget" across callees.** The
walk's counter (peaked ~10 for `is_even(10)`) is *the same counter*
across the cross-callee jumps. The reducer must not reset the budget
when descending into a different callee — otherwise `is_even`
unrolls 32 steps, then `is_odd` gets a fresh 32, and so on. The
all-or-nothing rule applies to the *top-level callsite* (e.g.
`is_even(10)` in main), not per-callee.

**Recommendation:** make this explicit in the reducer's budget docs:
the budget is per *top-level callsite reduction attempt*, not per
function.

**Bodies emitted by main:** **zero**. All four top-level calls reduce
to literal booleans.
</content>
</invoke>