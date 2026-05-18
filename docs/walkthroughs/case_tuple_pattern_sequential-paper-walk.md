# case_tuple_pattern_sequential — paper walk

Fixture: `fixtures/case_tuple_pattern_sequential/input.fz`. Expected
stdout:

```
7
0
0
7
7
0
```

This fixture exercises **`case` and `with` expressions** with tuple
patterns and an atom-literal fallback, called sequentially so that
each callsite's return narrows the next callsite's input flow. For the
reducer it's a probe of whether `case`/`with` falls under the same
pattern-matrix consumer as multi-clause `fn`.

## Source

```
fn f(v) do
  case v do
    {:ok, x} -> x
    :err -> 0
  end
end

fn g(v) do
  with {:ok, x} <- v do x else :err -> 0 end
end

fn main() do
  print(f({:ok, 7}))
  print(f(:err))
  print(f(:err))
  print(f({:ok, 7}))
  print(g({:ok, 7}))
  print(g(:err))
end
```

## Call 1 — `f({:ok, 7})`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | `f` has one clause matching any `v` → bind `v := {:ok, 7}` | 1 |
| 1.2 | substitute | body is `case v do {:ok, x} -> x; :err -> 0 end` with `v := {:ok, 7}` → `case {:ok, 7} do ... end` | 1 |
| 1.3 | dispatch (case) | scrutinee is the literal `{:ok, 7}`; arm 0 head `{:ok, x}` matches → bind `x := 7`; arm 1 rejected | 1 |
| 1.4 | substitute | case body → `x` → `7` | 1 |

**Reduced form:** `7`.

## Call 2 — `f(:err)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | `f` clause matches → `v := :err` | 1 |
| 2.2 | substitute | case → `case :err do ... end` | 1 |
| 2.3 | dispatch (case) | arm 0 head `{:ok, x}` rejects (`:err` is atom, not 2-tuple); arm 1 head `:err` matches → no bindings | 1 |
| 2.4 | substitute | → `0` | 1 |

**Reduced form:** `0`.

## Call 3 — `f(:err)` (repeat)

Identical to Call 2. **Reduced form:** `0`.

## Call 4 — `f({:ok, 7})` (repeat of Call 1)

Identical to Call 1. **Reduced form:** `7`.

## Call 5 — `g({:ok, 7})`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 5.1 | dispatch | `g` clause matches → `v := {:ok, 7}` | 1 |
| 5.2 | substitute | body → `with {:ok, x} <- {:ok, 7} do x else :err -> 0 end` | 1 |
| 5.3 | dispatch (with) | RHS `{:ok, 7}` against head `{:ok, x}` → matches → bind `x := 7` | 1 |
| 5.4 | substitute | with body → `x` → `7` | 1 |

**Reduced form:** `7`.

## Call 6 — `g(:err)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 6.1 | dispatch | `g` clause matches → `v := :err` | 1 |
| 6.2 | substitute | body → `with {:ok, x} <- :err do x else :err -> 0 end` | 1 |
| 6.3 | dispatch (with) | RHS `:err` against `{:ok, x}` → rejects; fall through to `else` matrix; arm `:err` matches | 1 |
| 6.4 | substitute | else body → `0` | 1 |

**Reduced form:** `0`.

## main, after reduction

```
fn main() do
  print(7); print(0); print(0); print(7); print(7); print(0)
end
```

Zero `f` bodies, zero `g` bodies.

## Findings

**`case` falls cleanly under the existing rules — with one extension.**
The design discussion says `fn` clauses and `case` are the same
pattern-matrix consumer. Mechanically this means: when `substitute`
walks a body and finds a `case` expression on a *known* scrutinee,
the reducer treats the case arms as a clause matrix and runs
`dispatch` on it.

The seven rules as written don't *quite* say this — `dispatch` is
defined for "the callee is a multi-clause fn." A literal reading
might force the reducer to ship a body for `case` evaluation.

**Recommendation:** extend `dispatch` to fire on **any pattern matrix
in callable position** — function clauses, `case` arms, `with` arms,
`with` `else` arms. The matrix structure is the same; the surrounding
syntax is sugar. This is what fz-ul4.43 (the unifying pattern matrix)
was about, and the reducer should consume it uniformly.

**`with` is `case` with a fallthrough.** `with {:ok, x} <- v do B else
Es end` is equivalent to `case v do {:ok, x} -> B; <Es...> end`. Once
the pattern matrix has unified these (per fz-ul4.43), the reducer
needs no special `with` handling.

**`do/end` form of `case`.** The fixture uses `case v do ... end`,
not a block. Both surface forms must lower to the same matrix shape
before the reducer sees them. Assumed handled upstream of the
reducer.

**Scrutinee binding (`case x = expr do ...`).** Not exercised here,
but for completeness: if a future fixture uses scrutinee binding, the
reducer needs to substitute the binding into the case body, then
dispatch on the bound value. Same shape, one extra substitute step.
Worth verifying when the matrix lands.

**Sequential calls don't change the picture for the reducer.** The
fixture's purpose (per README) is to stress the codegen cont-chain
across sequential calls with narrow returns. The reducer dissolves
every call to literals before the codegen ever runs, so the
cont-chain seam never arises in the reduced IR. The fz-i82 bug it
locks in is irrelevant post-reduction — there are no calls to widen.

**Bodies emitted by main:** **zero**.
</content>
</invoke>