# spec_ok — paper walk

Ticket family: `fz-RED.*`. Reducer rules: see
`red-0-ast-eval-paper-walk.md`.

Related ticket: `fz-RED.9` — `@spec` as a downstream-narrowing
contract. Also: `fz-ul4.31` (the original `@spec` parsing +
`spec_check::validate_specs`), `fz-jg5.12` discussion of @spec as a
firewall in `bodies-are-boundaries.md`.

This fixture is **the** test of how `@spec` interacts with the
reducer. It's small but loaded.

## The source

```
defmodule M do
  @spec add1(integer) :: integer
  fn add1(n), do: n + 1
end

fn main(), do: print(M.add1(41))
```

## The two possible reducer behaviors

`@spec` raises a design question for the reducer that none of the
seven rules name directly. We walk both interpretations and then
state which one the design picks.

### Interpretation A — `@spec` is a boundary

Treat `@spec`'d functions as opt-in boundaries: the user said "this
function returns `integer`," they are signaling that they want a
body. The reducer **does not look inside** `add1` for static inputs.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| A.1 | stop-opaque (spec-boundary variant) | `M.add1` has `@spec`; treat as boundary. Leave the call in place; the call's return Descr is the declared `integer` (not a literal). | 1 |

Result: `print(M.add1(41))` survives. One `add1` body emitted.

### Interpretation B — `@spec` is a constraint only

The `@spec` declares a *type contract*; reduction proceeds normally
when inputs are statically known, and the contract is just verified
(or used by downstream callers when reduction *can't* fully fold).

| Step | Rule | Detail | Counter |
|---|---|---|---|
| B.1 | dispatch | single clause, head `n` accepts `int_lit(41)` ⊆ `integer`. Bind `n := 41`. | 1 |
| B.2 | substitute | body `n + 1` → `41 + 1` | 1 |
| B.3 | fold-prim | `Add(int_lit(41), int_lit(1))` → `int_lit(42)` | 1 |
| B.4 | (validation) | check the folded result `int_lit(42)` ⊆ declared `integer`. Yes. | 1 |

Result: `print(42)`. Zero `add1` bodies.

## Which one does the design pick?

`fz-RED.9` (in `bodies-are-boundaries.md`, the ticket DAG section):

> **Reducer change:** stop at `@spec`'d calls unless they're
> trivially inlinable.

So the design picks **Interpretation A in general, with a
trivial-inline escape hatch**. "Trivially inlinable" is not
formally defined in RED.9; the spirit is "single-clause leaf
bodies, fully literal input, body is a fold" — exactly `add1`'s
shape.

The fixture `spec_ok` is named for verifying the declared spec
matches inferred behavior. Under either A or B, the output `42` is
produced — but the **body count differs**:

- Interpretation A (pure boundary): 1 `add1` body emitted.
- Interpretation B (no boundary): 0 `add1` bodies.
- RED.9-with-escape: depends on whether the reducer judges `add1`
  trivially inlinable. For this body (`n + 1`, single clause, no
  recursion), it almost certainly does.

## main, after reduction

Under RED.9's "trivial-inline" reading (most charitable):

```
fn main() do
  print(42)
end
```

Under pure-boundary reading:

```
fn main() do
  print(M.add1(41))
end
```

with one `add1` body emitted.

## Findings

**This is the fixture that surfaces the actual design tension.**
`@spec` plays a dual role in the design:

1. **Downstream-narrowing contract** (the firewall view in
   `bodies-are-boundaries.md`, "annotations narrow opacity"):
   when a *downstream* caller can't see into `add1`'s body
   because reduction stopped earlier, the caller still gets to use
   `integer` as the result Descr without walking the body. Pure
   benefit.

2. **Stop signal for the reducer** (RED.9's "stop at @spec'd
   calls unless trivially inlinable"): the user opted into a body
   for `add1`; respect that.

These two roles compose when input is opaque (caller couldn't
reduce anyway; spec narrows the return). They **conflict when
input is static** (the reducer *could* fold, but RED.9 says don't
unless trivial).

**The walk requires a judgment call: "is this trivially
inlinable?"** That's not one of the seven rules. It's a heuristic
the reducer needs.

**Proposed rule clarification for RED.9:**

> `stop-spec` (new rule): when the callee has a declared `@spec`
> and the body is not trivially inlinable, leave the call in place
> and use the declared spec as the call's return Descr.
>
> Trivial-inline criterion (proposed, needs ratification): single
> non-recursive clause + body is a chain of Prims over the
> parameters (no inner calls except other trivially-inlinable
> functions). Equivalent to "the body is a Prim expression tree."

If this criterion is adopted, `add1` qualifies (body is `Add(n,
1)` — a Prim expression tree). Interpretation B applies; reduction
proceeds; `print(42)` is the output.

**Open question for the design:** is `spec_ok`'s expected behavior
"zero bodies emitted" (Interp B / trivial-inline) or "one
`add1` body emitted with `print(M.add1(41))` surviving" (Interp A
strict)? This affects RED.6's re-blessing of `expected.specs`
for this fixture. The walk **does not resolve this** — it surfaces
the choice. The design discussion needs to ratify.

**Subtler question:** what if the body's *inferred* type is
**narrower** than the declared spec? E.g., `@spec add1(integer) ::
integer` but the body provably returns `integer ∩ {non-negative}`
for non-negative input. The design contract says downstream callers
see the **declared** type, not the inferred one — the spec is the
firewall. The reducer, when it does fold through (trivial-inline
case), produces a literal Descr that's necessarily narrower than
the declared spec, and that's fine: the literal is a subtype of
the declared `integer`. **No conflict.** But: a downstream
*caller* that depended on the declared spec for its own narrowing
will see a strictly tighter Descr after reduction. That's a
strict improvement, but it means the spec-as-firewall property
is "the declared type is an *upper* bound on what downstream sees,
not an exact match." Worth being explicit.

**Three findings to take away:**

1. The seven rules don't name `@spec` handling. **RED.9 needs at
   minimum a `stop-spec` rule.** Whether it fires unconditionally
   or only when the body isn't trivially inlinable is a design
   choice.

2. **"Trivially inlinable" is a judgment heuristic** — it must be
   defined precisely (proposed: single-clause Prim-tree body) or
   replaced with an unconditional stop. Either resolves the
   ambiguity surfaced by this walk.

3. The `inferred ⊆ declared` check (today's
   `spec_check::validate_specs`) is **still needed** after
   reduction lands. For `spec_ok`, the inferred return of
   `add1`'s body is `int_lit(42)` at the only reachable callsite
   — provably `⊆ integer`. Validation passes. The check operates
   on the residual spec set, smaller than today's but
   structurally identical.

This is the most interesting fixture in the batch and deserves the
explicit design ratification it surfaces.
