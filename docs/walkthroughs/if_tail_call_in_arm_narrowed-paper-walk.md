# if_tail_call_in_arm_narrowed — paper walk

Ticket family: `fz-RED.*`. Reducer rules: see
`red-0-ast-eval-paper-walk.md`.

This fixture exercises **per-callsite narrowing of an if-cond**:
each call to `pick` supplies a literal `n`, so the `n == 0` cond
folds and one arm survives per callsite.

## The source

```
fn helper(), do: 7

fn pick(n) do
  if n == 0 do helper() else 99 end
end

fn main() do
  print(pick(0))
  print(pick(1))
end
```

## Call 1 — `pick(0)`

Input Descr: `int_lit(0)`.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | single clause, head `n` — accepts. Bind `n := 0`. | 1 |
| 1.2 | substitute | body `if n == 0 do helper() else 99 end` → `if 0 == 0 do helper() else 99 end` | 1 |
| 1.3 | fold-prim | `Eq(int_lit(0), int_lit(0))` → `true` | 1 |
| 1.4 | fold-prim (if-fold) / dispatch-on-bool | `If(true, then, else)` → `then` arm: `helper()` | 1 |
| 1.5 | recurse | `helper()` is non-recursive, no args; reduce it | 2 |
| 1.5.1 | dispatch | single clause; no params | 2 |
| 1.5.2 | substitute | body is the literal `7` | 2 |
| 1.5.3 | fold-prim | already literal | 2 |
| 1.6 | (sub-result) | `pick(0)` reduces to `7` | 2 |

## Call 2 — `pick(1)`

Input Descr: `int_lit(1)`.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | single clause, head `n` — accepts. Bind `n := 1`. | 1 |
| 2.2 | substitute | body → `if 1 == 0 do helper() else 99 end` | 1 |
| 2.3 | fold-prim | `Eq(int_lit(1), int_lit(0))` → `false` | 1 |
| 2.4 | fold-prim (if-fold) | `If(false, T, E)` → `else` arm: literal `99` | 1 |
| 2.5 | (sub-result) | `pick(1)` reduces to `99` | 1 |

## main, after reduction

```
fn main() do
  print(7)
  print(99)
end
```

Zero `pick` bodies emitted. **Zero `helper` bodies emitted** —
`pick(0)`'s arm inlined `helper()` and folded; no other callsite
references `helper`.

## Findings

**Per-callsite reduction is automatic.** Each call to `pick`
reduces independently, with its argument substituted into the
cond. The two callsites produce two distinct reductions; neither
forces a `pick` body. Compare today's pipeline (per the fixture's
History note), where the per-callsite specialization combined
with a lowering bug *silently dropped* the second print.

The reducer's **two universes property** holds here: if any
callsite supplied an opaque `n`, that callsite would `stop-opaque`
inside `pick` (or even before — `n == 0` against opaque int can't
fold), and `pick` would get a body for the opaque-n shape. Static
callers still reduce.

The "if-fold" same naming-gap from `if_constant_cond_with_call`
applies (use `dispatch` over a bool-matrix, or extend
`fold-prim`). Otherwise the walk is mechanical.

**Helper transitively dead.** Because `pick(0)` reduced to the
literal `7`, `helper` is never called from `main`'s reduced form.
The design's "bodies = boundaries" predicate gives zero bodies.
Existing reachable-spec BFS already handles this; nothing new.

No new judgment calls beyond the if-fold naming clarification.
