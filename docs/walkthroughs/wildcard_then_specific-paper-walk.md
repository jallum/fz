# wildcard_then_specific — paper walk

Fixture: `fixtures/wildcard_then_specific/input.fz`. Expected stdout:

```
:anything
:anything
:anything
:anything
```

This fixture locks in **first-match-wins** semantics: a wildcard
clause that precedes a more specific clause shadows it entirely.
Every input — including `0`, which the second clause would also match
— must dispatch to the first (wildcard) clause.

## Source

```
fn catch(_), do: :anything
fn catch(0), do: :zero

fn cmatch(v) do
  case v do
    _ -> :anything
    0 -> :zero
  end
end

fn main() do
  print(catch(0))
  print(catch(7))
  print(cmatch(0))
  print(cmatch(99))
end
```

## Call 1 — `catch(0)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | clause 0 head `_` matches → no bindings. **First match wins; clause 1 is not even tried.** | 1 |
| 1.2 | substitute | body → `:anything` | 1 |

**Reduced form:** `:anything`.

## Call 2 — `catch(7)`

Identical to Call 1 (clause 0 matches `_` against any input).
**Reduced form:** `:anything`.

## Call 3 — `cmatch(0)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 3.1 | dispatch | `cmatch` clause matches → `v := 0` | 1 |
| 3.2 | substitute | body → `case 0 do _ -> :anything; 0 -> :zero end` | 1 |
| 3.3 | dispatch (case) | arm 0 head `_` matches → no bindings. **First match wins.** | 1 |
| 3.4 | substitute | → `:anything` | 1 |

**Reduced form:** `:anything`.

## Call 4 — `cmatch(99)`

Identical shape to Call 3. **Reduced form:** `:anything`.

## main, after reduction

```
fn main() do
  print(:anything); print(:anything); print(:anything); print(:anything)
end
```

Zero `catch` bodies. Zero `cmatch` bodies. The `:zero` clauses in both
forms are **dead code**.

## Findings

**Source order is load-bearing.** Per the README (and fz-ul4.45):
"Source order is preserved by sorting sub-matrix rows by body_id at
every specialization step." The reducer's `dispatch` rule must walk
clauses in source order and commit to the first match. Maranget-style
matrix specialization can re-order rows for compilation efficiency;
that reordering must not bubble up to the reducer's dispatch result.

**Recommendation:** the reducer-side contract for `dispatch` should
explicitly say "returns the *lowest-index* matching clause." The
pattern matrix produced by fz-ul4.43 should expose this in the API
shape (e.g., `dispatch` returns `MatchedClause(min_idx, ...)`, not
just "some matching clause").

**Dead clauses survive in the IR.** Clause 1 of `catch` (the `0 ->
:zero` case) is unreachable in this fixture. The reducer doesn't
*delete* it from the IR — it just never dispatches to it. If
`reachable_specs` BFS (fz-ul4.42) handles dead-clause pruning
post-reduction, the residual binary won't contain the dead clause's
code. If not, it ships as dead code.

This is a minor cleanliness concern, not a correctness one. Worth
verifying when the reducer lands.

**`_` as a wildcard always matches.** No constraint on the input
Descr — even an opaque `any` would match. This means **stop-opaque
will essentially never fire if a wildcard appears before any specific
clauses**, because the wildcard's match doesn't depend on the input
shape. This is the "first-match-wins makes the matrix monotone" property
the pattern compiler should already enforce.

**Bodies emitted by main:** **zero**.
</content>
</invoke>