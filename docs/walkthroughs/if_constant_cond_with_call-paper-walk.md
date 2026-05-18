# if_constant_cond_with_call — paper walk

Ticket family: `fz-RED.*`. Reducer rules: see
`red-0-ast-eval-paper-walk.md`.

This fixture is the **constant-cond if** case: the condition folds
to `false`, so only the else-arm reaches `main`'s effective body.
The then-arm's `helper()` call should not survive reduction — it's
on a dead branch.

## The source

```
fn helper(), do: 7

fn main() do
  if 1 == 0 do
    print(helper())
  else
    print(99)
  end
end
```

## main — top-level evaluation

There is one syntactic top-level expression: the `If` whose
condition is `1 == 0`.

### Step A — fold the condition

| Step | Rule | Detail | Counter |
|---|---|---|---|
| A.1 | fold-prim | `Eq(int_lit(1), int_lit(0))`. Same kind, distinct bits → `false`. | 1 |

### Step B — fold the if

The reducer needs an **if-then-else fold** rule: when the condition
is a literal bool, replace the `If` with the corresponding arm
body. RED.0's seven rules don't name this explicitly — `fold-prim`
is the closest fit, treating `If(bool_lit, then, else)` as a
control-flow Prim. We'll record this as a fold-prim variant.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| B.1 | fold-prim (if-fold) | `If(false, T, E)` → `E`. Drop the then-arm entirely. | 1 |

### Step C — the surviving body is `print(99)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| C.1 | stop-opaque (extern) | `print(99)` — extern boundary; literal in hand | 1 |

The dropped then-arm contained `print(helper())`. **`helper` is
never reached from main after reduction.** Per the design contract
("bodies = opacity boundaries"), `helper` is not emitted.

## main, after reduction

```
fn main() do
  print(99)
end
```

Zero `helper` bodies. The then-arm's CPS-split continuation
machinery is unreachable.

## Findings

**Naming gap in the seven rules.** RED.0's table lists `fold-prim`
for Prims and `dispatch` for fn callees, but doesn't separately
name **if-then-else folding** as a rule. The README for this
fixture references the lowering's per-arm continuation-fn split
(fz-duq.2) — so structurally, after lowering, `main` doesn't have
a raw `If` expression; it has `TailCall(cont_for_if, [cond])`
followed by two branch fns. The reducer's `if` fold is therefore
really:

> When `cond` is a literal bool, the `If`'s outgoing `TailCall`
> can be replaced by a direct `TailCall` to the chosen arm's fn,
> and the unchosen arm becomes unreachable.

This is **dispatch-on-bool**, exactly parallel to dispatch on a
tuple shape. **Proposed rule clarification:** treat `If`-on-literal
as a special case of `dispatch` (over a two-element clause matrix
keyed by bool). That keeps the seven rules intact; the bool is
just a degenerate Descr.

Alternative phrasing: `fold-prim` for `If(bool_lit, T, E)`.
Functionally equivalent. Either way, **the reducer must reach
inside `If`/`If`-lowered continuations to fire this fold.** Since
fz-duq.2 puts each arm in its own fn, the reduction step is
mechanical: rewrite the outer fn's terminator from
`If(cond_bool_lit, then_fn, else_fn)` (or its lowered
`TailCall`-of-if-cont form) into `TailCall(else_fn)` directly when
`cond_bool_lit = false`.

**Dead-arm tracking.** Once the if folds, the then-arm fn becomes
unreachable from any root. The existing `reachable_specs` BFS
(fz-ul4.42) already prunes it; reduction shrinks the reachable set
even further. No new mechanism needed for dead-arm cleanup — it
falls out of existing reachability.

The walk is mechanical given the "If-on-literal is dispatch"
clarification. **Recommendation:** RED.0's rule table should
either add an `if-fold` row or explicitly note that bool dispatch
is the `dispatch` rule applied to a two-element bool matrix.
