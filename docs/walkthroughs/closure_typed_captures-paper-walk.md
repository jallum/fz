# closure_typed_captures — paper walk

Fixture: `fixtures/closure_typed_captures/input.fz`. Expected output:
`42`.

This walkthrough drives the lone `main` callsite through the reducer
rules by hand. This fixture introduces **non-trivial captures**: the
inner lambda captures `x` and `y` from `add_to`'s scope. Both end up
being literal Descrs at the callsite — so the closure dissolves
entirely.

## The source

```
fn add_to(x, y), do: fn (z) -> x + y + z
fn apply1(f, x), do: f(x)

fn main() do
  print(apply1(add_to(10, 20), 12))
end
```

Naming: call the anonymous fn `L` (the design doc calls it
`lambda_3`). `L` has parameter `z` and captures `[x, y]`. So
`add_to(x, y)` returns `closure_lit(L, [x, y])` — at the typer level,
`Prim::MakeClosure(L, [x, y])`.

## Call 1 — `apply1(add_to(10, 20), 12)`

Inside-out reduction of the argument first.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | `add_to` single clause → bind `x := 10`, `y := 20` | 1 |
| 1.2 | substitute | body `fn (z) -> x + y + z` becomes `MakeClosure(L, [10, 20])` after capture substitution | 1 |
| 1.3 | fold-prim | `MakeClosure(L, [literal, literal])` folds to the literal Descr `closure_lit(L, [10, 20])` (note A) | 1 |
| → | | argument is now the literal `closure_lit(L, [10, 20])` | |
| 1.4 | dispatch | `apply1` single clause → bind `f := closure_lit(L, [10, 20])`, `x := 12` | 2 |
| 1.5 | substitute | body `f(x)` → `closure_lit(L, [10, 20])(12)` | 2 |
| 1.6 | closure-inline | callee is a literal closure_lit → translate to `L(10, 20, 12)` (captures preconcat'd to args; see Findings) | 3 |
| 1.7 | dispatch | `L` single clause; params `x, y, z` (captures first, then arg) → bind `x := 10`, `y := 20`, `z := 12` | 3 |
| 1.8 | substitute | body `x + y + z` → `10 + 20 + 12` | 3 |
| 1.9 | fold-prim | `10 + 20 + 12` → `42` | 3 |

**Reduced form:** `42`.

## main, after reduction

```
fn main() do
  print(42)
end
```

Zero user-fn bodies. Zero heap allocations — the `MakeClosure` call
never executes at runtime because its result was folded to a literal
Descr that's only consumed by closure-inline at compile time.

## Structural-decrease check

No recursion.

## Findings

**The walk is mechanical end-to-end** — but it surfaces **two** sub-
rules not explicitly enumerated in the seven:

1. **fold-prim on `MakeClosure`** (step 1.3). The seven rules describe
   fold-prim as "a Prim whose inputs are all literal Descrs returns a
   literal Descr." `MakeClosure(F, [literal captures])` fits that shape
   exactly — but its output is a `closure_lit(F, [...])` Descr, which
   isn't a scalar literal. As long as the type lattice admits
   `closure_lit` Descrs as "literal" (the IR already does — see
   `closure_lit` in the existing pipeline), fold-prim handles this.
   **It's not a new rule; it's a clarification that "literal Descr"
   includes closure_lit forms.**

2. **closure-inline** (step 1.6). Same observation as in `higher_order`
   and `apply2`: when the callee operand of a `Call` is a literal
   `closure_lit(F, captures)`, the reducer rewrites the call to
   `F(captures ++ args)` and dispatches on `F`. With non-empty
   captures, this is where the captures dissolve into substitute. I
   recommend naming this as an explicit 8th rule.

**Mixed captures (out of scope here, but flagged).** If only one of
the captures had been a literal — say `add_to(10, opaque_y)` — then
`fold-prim` on `MakeClosure` would not produce a fully-literal
closure_lit. The result would be `closure_lit(L, [10, <opaque>])`,
which is *partly* known. The reducer can still inline `L`'s body
substituting the known capture (`10`) and leaving the opaque one as a
parameter. This is the "Issue 4" case in the design doc. Not
exercised by this fixture, but the rule set must handle it.

**Predicted shape:** 0 user bodies, 0 allocations. Matches the design-
doc table ("static captures dissolve").

**Note on the existing README.** The fixture's README describes the
*current* compiler's behavior — closure heap object, stub_fp, tail-CC
call_indirect. **Under the proposed reducer, none of that survives.**
The closure dissolves at compile time; the call lands as
`print(42)`. The README's behavior is what we should expect from a
*boundary body* version of this code (e.g. if `add_to` were called
with opaque arguments), not from main's static call.
