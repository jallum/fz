# vr5a_cross_kind_eq — paper walk

Ticket family: `fz-RED.*` (paper walk; this batch is type narrowing
& dispatch). Reducer rules: see `red-0-ast-eval-paper-walk.md`.

This fixture exercises **cross-kind equality folding**: the operands
of `==` lie on disjoint type axes (int vs atom). VR.5a today folds
this at codegen; the question is whether the reducer can fold it
upstream, in the Module pass.

## The source

```
fn main() do
  print(1 == :ok)
end
```

## Call 1 — `1 == :ok`

This is a `Prim::Eq` (or equivalent) with two literal Descr inputs.
There's no user function call to dispatch on; the reducer's only
relevant rule is `fold-prim`.

Input Descrs: `int_lit(1)`, `atom_lit(:ok)`.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | fold-prim | `Eq(int_lit(1), atom_lit(:ok))`. The kinds are disjoint (int axis ∩ atom axis = ⊥). By set-theoretic semantics of `==`, the result is statically `false`. Fold to `bool_lit(false)`. | 1 |

**Reduced form for the `==`:** literal `false`.

## Call 2 — `print(false)`

`print` is an extern / native call — the reducer **stops** here
(extern boundary; output Descr declared by host). No further
reduction of `print` itself. But its argument is now a literal.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | stop-opaque (extern variant) | `print` is extern; we leave the call in place but feed it the folded literal | — |

## main, after reduction

```
fn main() do
  print(false)
end
```

## Findings

**This fixture stresses `fold-prim` on a typed predicate, not on
arithmetic.** The seven-rule wording in RED.0 says fold-prim fires
when "inputs are all literal Descrs." That phrasing covers this
case naturally for `Eq` provided the reducer's fold-prim is built
to know:

> For `Eq(a, b)`: if `kind(a) ∩ kind(b) = ⊥` then `false`; else
> if both are literal same-kind values, compare bits.

This is **not arithmetic** — it's a disjointness query into the
type lattice. **Worth calling out:** the reducer's `fold-prim`
must consult the Descr lattice for `Eq`/`Neq`, not just literal
table-lookup. VR.5a today does this at codegen; reproducing it in
the reducer requires the same kind-disjointness check, ported up.
This is a mild generalization of fold-prim's contract.

No new rule needed — but the **fold-prim implementation must know
about the type lattice for `==`/`!=`**, which is more than naive
constant folding. Flagging for RED.1 implementation: fold-prim
needs the same disjointness oracle the codegen has today.

The existing VR.5a-emitted lint ("dead-binop") is a typer-side
concern, not a reducer concern; the reducer's job is only to fold
the value. Lint emission stays where it is.

No judgment calls outside the type-lattice consultation. The arc
is mechanical given that consultation as a primitive.
