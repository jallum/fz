# classify_two_clause — paper walk

Fixture: `fixtures/classify_two_clause/input.fz`. Expected stdout:

```
:zero
:other
```

The simplest **literal-vs-wildcard** dispatch — one literal head and
one wildcard catch-all.

## Source

```
fn classify(0), do: :zero
fn classify(_), do: :other

fn main() do
  print(classify(0))
  print(classify(7))
end
```

## Call 1 — `classify(0)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | clause 0 head `0` matches literal `0` → no bindings | 1 |
| 1.2 | substitute | body → `:zero` | 1 |

**Reduced form:** `:zero`.

## Call 2 — `classify(7)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | clause 0 rejects (`7 ≠ 0`); clause 1 head `_` matches → no bindings | 1 |
| 2.2 | substitute | body → `:other` | 1 |

**Reduced form:** `:other`.

## main, after reduction

```
fn main() do
  print(:zero)
  print(:other)
end
```

Zero `classify` bodies.

## Findings

**Two-clause literal-vs-wildcard dispatch is the smallest non-trivial
matrix.** Every step is exactly one of the seven rules; no judgment
calls. Both inputs are statically-known literal ints, so dispatch
always commits to a single clause.

**The wildcard `_` never produces a binding.** This is by convention
(`_` is the "ignore" pattern, not a named binding). The reducer needs
to know not to materialize a binding for it. Trivial detail; named
here for completeness.

**What if the input were an opaque `int`?** Then dispatch can't
commit — clause 0 *might* match if the int is `0`, but the reducer
can't prove it. **stop-opaque** fires; one body is emitted for
`classify(int)`. Not exercised in this fixture but worth flagging as
the natural failure mode.

**Bodies emitted by main:** **zero**.
</content>
</invoke>