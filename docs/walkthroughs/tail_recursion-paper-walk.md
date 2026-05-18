# tail_recursion — paper walk

Fixture: `fixtures/tail_recursion/input.fz`. Expected stdout:
`100000`.

This is the canonical **stop-budget** case. Literal input `100000`
would unroll cleanly in principle (it's a literal-int countdown, so
structural decrease holds at every step) — but the unroll budget is
32 by default. The all-or-nothing rule says: stop, abandon the partial
unrolling, leave the original top-level call in place. The reducer
emits **one** `count` body that runs at runtime.

## Source

```
fn count(0, acc), do: acc
fn count(n, acc), do: count(n - 1, acc + 1)

fn main() do print(count(100000, 0)) end
```

## Call 1 — `count(100000, 0)`

The reducer attempts reduction in a scratch buffer:

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | input `(100000, 0)`; clause 0 rejects (`100000 ≠ 0`); clause 1 matches → bind `n := 100000`, `acc := 0` | 1 |
| 1.2 | substitute | body → `count(100000 - 1, 0 + 1)` | 1 |
| 1.3 | fold-prim | → `count(99999, 1)` | 1 |
| 1.4 | recurse | literal `99999 < 100000` ✓ | 2 |
| 1.4.* | (same shape) | → `count(99998, 2)` | 2 |
| 1.5 | recurse | → `count(99997, 3)` | 3 |
| ... | ... | ... | ... |
| 1.32 | recurse | → `count(99968, 32)` | 32 |
| 1.33 | recurse | would step into `count(99967, 33)` — counter would become 33 | 33 |
| 1.34 | **stop-budget** | counter (33) exceeds `UNROLL_BUDGET` (32). **Abandon** the scratch buffer; **discard** the 32-step partial unrolling. | 33 |

**Reducer commits nothing.** The original top-level call —
`count(100000, 0)` — is left in place verbatim. A single body for
`count` is forced into existence, callable with the `(int, int)`
argument shape.

## main, after reduction

```
fn main() do print(count(100000, 0)) end
```

The IR is **identical to the source** for this call. One body
emitted: `count(int, int) -> int`.

## Findings

**The all-or-nothing policy fires cleanly.** Per
bodies-are-boundaries: "If reduction terminates within budget,
commit; otherwise discard the partial work and leave the original
call in place." This avoids two failure modes:

1. *Partial unrolling shipped as residual.* The user would get 32
   unrolled cons cells of CLIF plus a tail call to `count(99968, 32)`
   — surprising, hard to reason about, and bigger than the body call
   it replaces.
2. *Inconsistent budget-end states.* Different callsites would commit
   at different unrolling depths depending on their starting literal,
   producing wildly variable code shapes.

Discarding the partial work makes the cost model predictable: **either
this callsite is dissolved entirely or it's a single body call.** No
in-between.

**Structural decrease is provable, but doesn't help.** Each step's
literal-int decrement qualifies as structural decrease (compare to
`count(opaque_n, 0)` which would also hit **stop-non-decrease** at
step 1). Yet the budget caps unrolling. The two stop conditions are
independent — **stop-budget** is a cost-model cap, not a correctness
fence.

**The surviving call carries opaque or literal argument Descrs?**
The call-site argument is the *literal* `(100000, 0)`. But the body
that's emitted is the general `count(int, int) → int` body — there's
no callsite-specialization to `(100000, 0)`. Result: caller passes
literal `100000` and literal `0`; callee body accepts `(int, int)`.
Standard unboxed-int calling convention; no surprise.

**Bodies emitted by main:** **one** — `count`. This matches the
bodies-are-boundaries prediction table: `tail_recursion` is the
canonical "1 body, no heap allocations (int loop, unboxed)" entry.

**No new rules required.** **stop-budget** is exactly what the seven
rules call for; the walk uses it as advertised. This is the cleanest
case for verifying the rule's behavior because every preceding step
*does* qualify under `recurse` — the budget is the only thing that
stops it.

**Knob sensitivity.** If the user raised `UNROLL_BUDGET` to (say)
100001, this callsite would fully reduce to the literal `100000`.
The fixture's choice of `100000` is well-calibrated: comfortably
larger than any reasonable budget, while small enough to be a
realistic literal in source.
</content>
</invoke>