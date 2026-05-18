# if_tail_call_in_arm_unnarrowed — paper walk

Ticket family: `fz-RED.*`. Reducer rules: see
`red-0-ast-eval-paper-walk.md`.

Sibling of `if_tail_call_in_arm_narrowed`. Same shape, but the cond
is `n > 0` (a relational predicate). With literal `n` at each
callsite, the relational predicate **still folds** at the reducer
level — `>` over literals is fold-prim's bread and butter. The
fixture's README discusses this as a typer-narrowing question (the
typer doesn't narrow `n > 0` per-callsite); the reducer doesn't
need typer narrowing because it has the literal.

## The source

```
fn helper(), do: 7

fn pick(n) do
  if n > 0 do helper() else 99 end
end

fn main() do
  print(pick(5))
  print(pick(0))
end
```

## Call 1 — `pick(5)`

Input Descr: `int_lit(5)`.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | single clause, head `n` — accepts. Bind `n := 5`. | 1 |
| 1.2 | substitute | body → `if 5 > 0 do helper() else 99 end` | 1 |
| 1.3 | fold-prim | `Gt(int_lit(5), int_lit(0))` → `true` | 1 |
| 1.4 | fold-prim (if-fold) | `If(true, T, E)` → `helper()` | 1 |
| 1.5 | recurse | `helper()` — non-recursive nullary | 2 |
| 1.5.1 | dispatch | clause accepts | 2 |
| 1.5.2 | substitute | body is `7` | 2 |
| 1.6 | (sub-result) | `pick(5)` reduces to `7` | 2 |

## Call 2 — `pick(0)`

Input Descr: `int_lit(0)`.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | single clause, head `n` — accepts. Bind `n := 0`. | 1 |
| 2.2 | substitute | body → `if 0 > 0 do helper() else 99 end` | 1 |
| 2.3 | fold-prim | `Gt(int_lit(0), int_lit(0))` → `false` | 1 |
| 2.4 | fold-prim (if-fold) | `If(false, T, E)` → literal `99` | 1 |
| 2.5 | (sub-result) | `pick(0)` reduces to `99` | 1 |

## main, after reduction

```
fn main() do
  print(7)
  print(99)
end
```

Zero `pick` bodies. Zero `helper` bodies.

## Findings

**The reducer doesn't depend on typer narrowing for this shape.**
The fixture's README distinguishes itself from the narrowed sibling
on the grounds that the typer doesn't narrow `n > 0` per-callsite.
That distinction matters for the *typer's* clause-specialization
behavior; it doesn't matter for the *reducer*, because the reducer
has literal Descrs to work with at each callsite and can fold the
relational predicate directly. Both fixtures reduce to the same
shape (`print(7); print(99)`) with the same body count (zero), and
both walks are isomorphic.

This is a useful **negative result for the reducer's role**: the
reducer is largely indifferent to whether the typer would have
narrowed a particular cond, because reduction works on literal
Descrs flowing in from callsites, not on per-callsite specialized
type information about wider Descrs. The typer-narrowing question
matters for the *boundary body's* shape, not for the static-input
paths.

If `main` had supplied an opaque `n` instead, *then* typer
narrowing matters: it would determine whether `pick`'s arms get
specialized in the boundary body. That's a different concern from
the reducer's static-input behavior.

No judgment calls; same if-fold naming note as the sibling.
