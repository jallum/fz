# RED.0 SPIKE — ast_eval paper walk

Ticket: `fz-jg5.1` (SPIKE — verify the reducer algorithm before any
production code lands).

This walkthrough drives every `eval(...)` callsite in `main` through
the reducer rules **by hand**. The spike succeeds iff every step is
mechanical — one of the named rules — and we land at the correct
values (`42`, `14`, `21`).

If any step requires a judgment call we haven't named, the arc stops
here and re-designs. See § "Findings" at the bottom.

## The reducer rules, in one place

The reducer operates on a callsite `f(args)` in a caller's IR. At
each step it applies one of:

| Rule | When | Effect |
|---|---|---|
| **dispatch** | the callee is a multi-clause fn; try clause heads against the input Descrs | on success: yield `MatchedClause(idx, bindings)` and continue |
| **substitute** | a `MatchedClause` is in hand | replace pattern-bound names in the clause body with their bound Descrs |
| **fold-prim** | a `Prim` whose inputs are all literal Descrs | evaluate to a literal Descr |
| **recurse** | the substituted body contains a `Call`/`TailCall` whose input Descr is **strictly structurally smaller** than the parent's | reduce that call too (counter +1) |
| **stop-opaque** | `dispatch` reports no clause statically matches (Descr too wide) | leave the call in place; emit a body for the callee |
| **stop-non-decrease** | a recursive call's input Descr is not provably smaller than the parent's | leave the call in place |
| **stop-budget** | counter exceeds `UNROLL_BUDGET` (default 32) | abandon partial work, leave the **original top-level** call in place |

Structural-decrease measure: an input Descr `D'` is smaller than `D`
if it's a sub-Descr extracted by projection (tuple field, list head/
tail, pattern binding) of `D`. AST depth, tuple arity, list length
all qualify. Decrement of an opaque integer (`n - 1` where `n :: int`)
does **NOT** qualify — that's count_100k's case and the budget-bound
catches it.

## The source

```
fn eval({:num, n}), do: n
fn eval({:add, a, b}), do: eval(a) + eval(b)
fn eval({:mul, a, b}), do: eval(a) * eval(b)

fn main() do
  print(eval({:num, 42}))
  print(eval({:add, {:num, 2}, {:mul, {:num, 3}, {:num, 4}}}))
  print(eval({:mul, {:add, {:num, 1}, {:num, 2}}, {:add, {:num, 3}, {:num, 4}}}))
end
```

## Call 1 — `eval({:num, 42})`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | input `{:num, 42}`: clause 0 head `{:num, n}` matches → bind `n := 42` | 1 |
| 1.2 | substitute | body `n` → `42` | 1 |
| 1.3 | fold-prim | result is already a literal Descr `int_lit(42)` — nothing to fold | 1 |

**Reduced form:** `42` (literal). No call to `eval` remains.

## Call 2 — `eval({:add, {:num, 2}, {:mul, {:num, 3}, {:num, 4}}})`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | clause 0 `{:num, n}` rejects (head `:add` ≠ `:num`); clause 1 `{:add, a, b}` matches → bind `a := {:num, 2}`, `b := {:mul, {:num, 3}, {:num, 4}}` | 1 |
| 2.2 | substitute | body `eval(a) + eval(b)` → `eval({:num, 2}) + eval({:mul, {:num, 3}, {:num, 4}})` | 1 |
| 2.3 | recurse | reduce `eval({:num, 2})` — input strictly smaller (depth 1 vs 3) | 2 |
| 2.3.1 | dispatch | clause 0 matches → `n := 2` | 2 |
| 2.3.2 | substitute | `n` → `2` | 2 |
| → | | sub-result: `2` | |
| 2.4 | recurse | reduce `eval({:mul, {:num, 3}, {:num, 4}})` — strictly smaller (depth 2 vs 3) | 3 |
| 2.4.1 | dispatch | clauses 0, 1 reject; clause 2 `{:mul, a, b}` matches → `a := {:num, 3}`, `b := {:num, 4}` | 3 |
| 2.4.2 | substitute | body → `eval({:num, 3}) * eval({:num, 4})` | 3 |
| 2.4.3 | recurse | `eval({:num, 3})` → `3` | 4 |
| 2.4.4 | recurse | `eval({:num, 4})` → `4` | 5 |
| 2.4.5 | fold-prim | `3 * 4` → `12` | 5 |
| → | | sub-result: `12` | |
| 2.5 | fold-prim | `2 + 12` → `14` | 5 |

**Reduced form:** `14` (literal). Counter peaked at 5 — well under
budget (32). Zero residual calls.

## Call 3 — `eval({:mul, {:add, {:num, 1}, {:num, 2}}, {:add, {:num, 3}, {:num, 4}}})`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 3.1 | dispatch | clauses 0, 1 reject; clause 2 matches → `a := {:add, {:num, 1}, {:num, 2}}`, `b := {:add, {:num, 3}, {:num, 4}}` | 1 |
| 3.2 | substitute | body → `eval(a) * eval(b)` | 1 |
| 3.3 | recurse | reduce `eval({:add, {:num, 1}, {:num, 2}})` (depth 2 vs 3) | 2 |
| 3.3.1 | dispatch | clause 1 matches → `a := {:num, 1}`, `b := {:num, 2}` | 2 |
| 3.3.2 | substitute | body → `eval({:num, 1}) + eval({:num, 2})` | 2 |
| 3.3.3 | recurse | `eval({:num, 1})` → `1` | 3 |
| 3.3.4 | recurse | `eval({:num, 2})` → `2` | 4 |
| 3.3.5 | fold-prim | `1 + 2` → `3` | 4 |
| → | | sub-result: `3` | |
| 3.4 | recurse | reduce `eval({:add, {:num, 3}, {:num, 4}})` (depth 2 vs 3) | 5 |
| 3.4.* | (same shape as 3.3.*) | yields `7` | 8 |
| 3.5 | fold-prim | `3 * 7` → `21` | 8 |

**Reduced form:** `21` (literal). Counter peaked at 8. Under budget.
Zero residual calls.

## main, after reduction

```
fn main() do
  print(42)
  print(14)
  print(21)
end
```

The three `eval(...)` calls dissolved entirely. Zero `eval` bodies
are forced into existence by main. The compiled binary contains only
`main`, the three `print` calls' extern wrapper, and runtime shims.

## Structural-decrease check, in detail

The recurse rule fires only when the recursive call's input Descr is
provably smaller. In ast_eval, every recursive call inside a clause
body has the shape `eval(a)` or `eval(b)`, where `a` and `b` are
pattern-bound variables from the clause head — i.e., immediate
sub-terms of the input tuple. By construction the sub-term is
strictly smaller than the containing tuple.

This is the case the reducer needs to recognize. The check is
trivial when the input Descr is a literal tuple shape (depth and
arity are inspectable). It would NOT fire for:

- Opaque integer arithmetic: `count(n - 1, acc + 1)` where `n :: int`
  is not statically known to be smaller in any Descr-level sense.
  Result: stop-non-decrease (and/or stop-budget). count_100k gets
  a single `count` body. ✓
- Mutual recursion on integers: `is_even(n - 1)` where `n` is a
  literal `n_0` and `n - 1` constant-folds to `n_0 - 1`. *That*
  IS provably smaller (literal-decrement). So mutual_recursion(10)
  unrolls 10 steps (budget=32) and reduces fully. ✓ — this is the
  case the design discussion flagged as "literal int countdown
  reduces, opaque int decrement doesn't."

## Findings

**The walk is mechanical end-to-end.** Every step in every call
above is one of the seven named rules. No judgment calls surfaced.

**Three rules carry all the weight:**
- `dispatch` — needs the pattern matrix (fz-ul4.43) as input.
- `substitute` — straight IR rewrite; mechanical.
- `fold-prim` — constant folding; `ir_fold` already does this for
  blocks.

**Two rules are correctness fences:**
- `stop-opaque` — the type system tells us when to fire (Descr too
  wide to dispatch).
- `stop-non-decrease` / `stop-budget` — termination guarantees.

**One subtlety to remember:** structural-decrease distinguishes
"smaller literal" (e.g. `n_0 - 1` where `n_0` is a literal int) from
"smaller value of opaque type" (`n - 1` where `n :: int`). The first
qualifies as decrease; the second does not. mutual_recursion's
behavior depends on this distinction — call sites with literal int
starting values reduce; the same source with an opaque int argument
would not. This is by design (the "you don't get to unroll runtime
inputs" property), but worth being explicit about in the RED.4
implementation.

**Spike outcome: GO.** No hopeless issue surfaced. RED.1 (the
pattern reduction primitive) can proceed; RED.2 (clause dispatch)
will await fz-ul4.43; RED.3 onward layers on top.

## Tangential observation

While walking call 2, I noticed the reducer's natural traversal
order is **outside-in** at each callsite (dispatch the outermost
call first, then recurse on its arguments). This is the opposite of
the "leaves-up" framing in the design discussion — but the two are
the same algorithm seen from different ends. Leaves-up is what the
*caller* sees: leaves get resolved first because the reducer
descends to them first. Outside-in is what the *reducer* does step
by step. The doc's "leaves-up" framing is the right user-facing
mental model; the implementation is naturally outside-in.

This isn't a hopeless issue — it's a "be careful when writing the
RED.3 docs" reminder.
