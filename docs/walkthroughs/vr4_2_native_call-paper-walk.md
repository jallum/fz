# vr4_2_native_call — paper walk

Ticket family: `fz-RED.*`. Reducer rules: see
`red-0-ast-eval-paper-walk.md`.

This fixture is the classic **fully-reducible helper**: a leaf body
called once with a literal argument. Under today's pipeline it's a
showcase for the native ABI (VR.4.2). Under the proposed reducer
the call dissolves entirely — there's nothing left to call.

## The source

```
fn square(x) do
  x * x
end

fn main() do
  print(square(7))
end
```

## Call 1 — `square(7)`

Input Descr: `int_lit(7)`.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | single clause, head `x` (untyped) — accepts. Bind `x := 7`. | 1 |
| 1.2 | substitute | body `x * x` → `7 * 7` | 1 |
| 1.3 | fold-prim | `Mul(int_lit(7), int_lit(7))` → `int_lit(49)` | 1 |

**Reduced form:** `49`.

## main, after reduction

```
fn main() do
  print(49)
end
```

Zero `square` bodies emitted. The whole VR.4.2 native-ABI apparatus
becomes moot for this program — there's no callee left to invoke
through any calling convention. The CLIF should collapse to one
`print` extern call with a constant argument.

## Findings

This is the most strongly-reducible shape: single non-recursive
clause, literal input, body is a pure Prim chain. The reducer's
RED.3 scaffold (single non-recursive clause inline + statically
known input) handles it in three steps.

**Tension worth flagging:** VR.4.2 is a calling-convention
optimization — it makes `square` cheap to call. The reducer makes
`square` *not exist*. These are not adversarial: if `square` ever
sees an opaque argument (e.g. from another callsite), VR.4.2's
native ABI still applies to the boundary body. They compose. But
for this fixture **the native ABI win is unmeasurable** because
the call dissolves.

This is an instance of the design's central claim: "reduction is
the cheapest possible optimization for allocation — don't have
any" (`bodies-are-boundaries.md`). The same logic applies to call
overhead: don't have any.

No judgment calls. The seven rules cover this fixture trivially.
