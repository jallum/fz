# vr3_4_typed_capture — paper walk

Ticket family: `fz-RED.*`. Reducer rules: see
`red-0-ast-eval-paper-walk.md`.

This fixture exercises **continuation-captured typed values** across
a call. Under today's pipeline VR.3.4/VR.4.3 keep the captured `x`
in a native block param across the chain. Under the reducer, the
program reduces to a constant: `print(21)`.

## The source

```
fn double(x) do x * 2 end
fn use_x(x) do print(double(x) + x) end
fn main() do
  use_x(7)
end
```

## Top-level call — `use_x(7)`

Input Descr: `int_lit(7)`.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | single clause, head `x` untyped — accepts. Bind `x := 7`. | 1 |
| 1.2 | substitute | body `print(double(x) + x)` → `print(double(7) + 7)` | 1 |
| 1.3 | recurse | the substituted body contains `double(7)` whose input is a literal — strictly "structurally smaller" by the literal-arg measure (no opaque dependency). | 2 |

### Sub-call 1.3.x — `double(7)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.3.1 | dispatch | single clause, head `x` — accepts. Bind `x := 7`. | 2 |
| 1.3.2 | substitute | body `x * 2` → `7 * 2` | 2 |
| 1.3.3 | fold-prim | `Mul(int_lit(7), int_lit(2))` → `int_lit(14)` | 2 |

Returning to the parent context:

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.4 | fold-prim | `Add(int_lit(14), int_lit(7))` → `int_lit(21)` | 2 |
| 1.5 | stop-opaque (extern) | `print(21)` — extern boundary; leave the call, feed the literal | 2 |

## main, after reduction

```
fn main() do
  print(21)
end
```

Zero `use_x` or `double` bodies emitted. The "continuation captures
`x`" engineering is unnecessary because no continuation survives.

## Findings

**Structural-decrease question.** RED.0's structural-decrease
measure is defined for projection out of a tuple/list. Here the
"recursive descent" at step 1.3 isn't recursion at all — it's
descent into a *non-recursive* helper (`double`) whose input is a
literal. The RED.3 scaffold ("single non-recursive clause inline +
statically known input") handles this without needing the decrease
check at all. The `recurse` rule's structural-decrease wording is
strictly the *recursive* descent guard; non-recursive descent is
always permitted (it terminates by call-graph acyclicity).

This is worth being explicit about: **the reducer's "recurse" rule
is overloaded** — it covers both (a) recursive calls with literal
descent and (b) plain non-recursive subcall reduction. The
structural-decrease check applies only to (a). For (b), pure
acyclicity of the call graph is the termination guarantee. The
implementation likely already separates these, but RED.0's table
folds them together for brevity. Flagging for clarity.

No new rule needed. No judgment calls. The fixture reduces
mechanically; the VR.3.4 captured-cont machinery has nothing to
operate on after reduction.
