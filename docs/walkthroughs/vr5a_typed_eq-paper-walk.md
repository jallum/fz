# vr5a_typed_eq — paper walk

Ticket family: `fz-RED.*`. Reducer rules: see
`red-0-ast-eval-paper-walk.md`.

This fixture is the **same-kind** sibling of `vr5a_cross_kind_eq`:
literal int/int and atom/atom equality. Every comparison's inputs
are literal Descrs, so the reducer should fold all four.

## The source

```
fn main() do
  print(1 == 2)
  print(1 == 1)
  print(:ok == :err)
  print(:ok == :ok)
end
```

## Call 1 — `1 == 2`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | fold-prim | `Eq(int_lit(1), int_lit(2))`. Same kind, distinct bit values → `false` | 1 |

## Call 2 — `1 == 1`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | fold-prim | `Eq(int_lit(1), int_lit(1))`. Same kind, equal bits → `true` | 1 |

## Call 3 — `:ok == :err`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 3.1 | fold-prim | `Eq(atom_lit(:ok), atom_lit(:err))`. Same kind (atom), distinct interned ids → `false` | 1 |

## Call 4 — `:ok == :ok`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 4.1 | fold-prim | `Eq(atom_lit(:ok), atom_lit(:ok))`. Same kind, equal interned ids → `true` | 1 |

## main, after reduction

```
fn main() do
  print(false)
  print(true)
  print(false)
  print(true)
end
```

Four `print` extern calls remain (boundary). Zero `Eq` operations
survive.

## Findings

Pure fold-prim arc, four times. **Mechanical.** Same notice as in
`vr5a_cross_kind_eq`: fold-prim for `==` must consult kind first,
then bit-equality (or atom-id equality) within the kind. This is
the well-behaved same-kind branch — no surprises.

A subtlety worth recording: `Eq(int_lit, atom_lit)` (cross-kind)
and `Eq(int_lit, int_lit)` (same-kind, value differs) both fold to
`false` but **for different reasons**. The reducer's fold-prim
shouldn't fuse these into one "is it equal?" path — the kind check
must come first, because for opaque operands of two known-disjoint
kinds the answer is *still* statically `false` even though no
literal bit comparison is possible. (This fixture doesn't hit
that case; the cross-kind fixture nearly does but uses literals on
both sides.)

No judgment calls. No rules missing.
