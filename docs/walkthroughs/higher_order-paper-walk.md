# higher_order — paper walk

Fixture: `fixtures/higher_order/input.fz`. Expected output: `42`,
`-7`, `-10`.

This walkthrough drives every callsite in `main` through the reducer
rules by hand. The interesting move: top-level fn names like
`double` and `neg`, when passed as values, become zero-capture
`closure_lit(F, [])` Descrs. The reducer treats them as known
callees.

## The source

```
fn double(x), do: x * 2
fn neg(x), do: 0 - x
fn apply2(f, x), do: f(x)
fn compose(f, g, x), do: f(g(x))

fn main() do
  print(apply2(double, 21))
  print(apply2(neg, 7))
  print(compose(double, neg, 5))
end
```

The names `double`, `neg` appearing as arguments are sugar for
`closure_lit(double, [])`, `closure_lit(neg, [])` — the typer fires
`Prim::MakeClosure` with zero captures.

## Call 1 — `apply2(double, 21)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | `apply2`: single clause, binders `f, x` always match → bind `f := closure_lit(double, [])`, `x := int_lit(21)` | 1 |
| 1.2 | substitute | body `f(x)` → `closure_lit(double, [])(21)` | 1 |
| 1.3 | recurse | the callee Descr is a literal `closure_lit(double, [])`; dispatch on the closure_lit (note A) → reduce `double(21)` | 2 |
| 1.3.1 | dispatch | `double`: single clause, binder `x` → bind `x := 21` | 2 |
| 1.3.2 | substitute | body `x * 2` → `21 * 2` | 2 |
| 1.3.3 | fold-prim | `21 * 2` → `42` | 2 |

**Reduced form:** `42`. No `apply2` or `double` body needed.

**Note A — closure_lit dispatch:** when the callee operand of a
`Call` reduces to a literal `closure_lit(F, captures)` Descr, the
reducer treats it as an alias for `F` with the captures preconcat'd
to the argument list. With zero captures this is simply: dispatch on
`F`. This is `dispatch` operating on closure_lit-as-callee; the
seven rules don't explicitly enumerate it, but it falls under the
same rule mechanically (see Findings).

## Call 2 — `apply2(neg, 7)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | `apply2` clause matches → `f := closure_lit(neg, [])`, `x := 7` | 1 |
| 2.2 | substitute | body → `closure_lit(neg, [])(7)` | 1 |
| 2.3 | recurse | reduce `neg(7)` via closure_lit dispatch | 2 |
| 2.3.1 | dispatch | `neg` clause matches → `x := 7` | 2 |
| 2.3.2 | substitute | body `0 - x` → `0 - 7` | 2 |
| 2.3.3 | fold-prim | `0 - 7` → `-7` | 2 |

**Reduced form:** `-7`.

## Call 3 — `compose(double, neg, 5)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 3.1 | dispatch | `compose`: single clause, binders `f, g, x` → bind `f := closure_lit(double, [])`, `g := closure_lit(neg, [])`, `x := 5` | 1 |
| 3.2 | substitute | body `f(g(x))` → `closure_lit(double, [])(closure_lit(neg, [])(5))` | 1 |
| 3.3 | recurse | reduce the inner call `neg(5)` first (it's the argument to the outer; structurally a sub-expression) | 2 |
| 3.3.1 | dispatch | `neg` matches → `x := 5` | 2 |
| 3.3.2 | substitute | `0 - x` → `0 - 5` | 2 |
| 3.3.3 | fold-prim | `0 - 5` → `-5` | 2 |
| 3.4 | recurse | outer call now `closure_lit(double, [])(-5)` → reduce `double(-5)` | 3 |
| 3.4.1 | dispatch | `double` matches → `x := -5` | 3 |
| 3.4.2 | substitute | `x * 2` → `-5 * 2` | 3 |
| 3.4.3 | fold-prim | `-5 * 2` → `-10` | 3 |

**Reduced form:** `-10`.

## main, after reduction

```
fn main() do
  print(42)
  print(-7)
  print(-10)
end
```

Zero user-fn bodies emitted. The names `double`, `neg`, `apply2`,
`compose` never produce a body — every callsite collapsed.

## Structural-decrease check

No recursive call sites in this fixture. The reduction is purely
"outside-in inline-and-fold," with the closure_lit indirection
unwound at step 1.3 / 2.3 / 3.3 / 3.4.

## Findings

**The walk is mechanical end-to-end** — but it relies on a sub-rule
that the seven rules name only implicitly: **closure_lit-as-callee
dispatch**. When the callee operand of a `Call` is a literal
`closure_lit(F, captures)` Descr, the reducer:

1. Prepends `captures` to the argument list (here: zero captures, so
   no change).
2. Dispatches on `F` as if the call had been `F(args)` directly.

This is what the design doc means by "static captures dissolve" —
the captures vanish into substitute, and the dispatch lands on the
underlying function body.

**Naming question.** The seven rules list `dispatch` as "the callee
is a multi-clause fn." That phrasing assumes the callee is a
function *name*. When the callee is a `closure_lit` Descr, we still
do dispatch — but on the function the closure_lit points to. We can
either:

- Read `dispatch` broadly: "the callee's static identity is known
  (either a name or a closure_lit)." This requires no new rule.
- Add a named sub-rule **closure-inline** that translates a
  `closure_lit(F, captures)` callee to a direct `F(captures ++
  args)` call and then defers to `dispatch`.

The mechanical work is identical. The second framing is more honest
to the IR — `Call` distinguishes callee-by-name from callee-by-value
— and makes the closure path auditable in diagnostics. **My
recommendation: add closure-inline as an explicit 8th rule, even
though it's mechanically a special case of substitute + dispatch.**

**No structural-decrease subtlety.** No recursion in this fixture.

**Predicted shape:** 0 user bodies, 0 allocations. Matches the
design-doc table.
