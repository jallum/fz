# modules — paper walk under the RED.0 reducer

Driving every callsite in `main` through the seven reducer rules from
`red-0-ast-eval-paper-walk.md`. Paper exercise; no compile/run.

Expected output: `42`, `20`, `107`.

## The source

```
defmodule M do
  fn double(x), do: x * 2
  fn quad(x), do: double(double(x))
end

defmodule N do
  fn helper(x), do: x + 100
end

fn main() do
  print(M.double(21))
  print(M.quad(5))
  print(N.helper(7))
end
```

Module structure: two flat top-level modules `M` and `N`. After name
resolution these are simply qualified fn names in a single `Module`
IR — `M.double`, `M.quad`, `N.helper`. The reducer sees three fns, one
clause each, plus `main`. There is no recursion and every clause has a
single pattern that is a plain variable binding (no shape narrowing
needed).

## Call 1 — `M.double(21)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | `M.double` has one clause `double(x)`; var pattern matches any input → bind `x := 21` | 1 |
| 1.2 | substitute | body `x * 2` → `21 * 2` | 1 |
| 1.3 | fold-prim | `21 * 2` → `42` | 1 |

**Reduced form:** `42` (literal). Counter 1. Zero residual `M.double`
body calls forced by this site.

## Call 2 — `M.quad(5)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | `M.quad` single clause `quad(x)` → bind `x := 5` | 1 |
| 2.2 | substitute | body `double(double(x))` → `double(double(5))` | 1 |
| 2.3 | recurse | reduce inner `double(5)` — argument literal, strictly smaller than the parent's call shape (literal int vs. an opaque call result). Treat literal scalars as already-reduced; the recurse rule fires on the *call*, not on a structural sub-Descr. See Findings. | 2 |
| 2.3.1 | dispatch | `double` clause → `x := 5` | 2 |
| 2.3.2 | substitute | body `x * 2` → `5 * 2` | 2 |
| 2.3.3 | fold-prim | `5 * 2` → `10` | 2 |
| → | | sub-result: `10` | |
| 2.4 | recurse | reduce outer `double(10)` | 3 |
| 2.4.1 | dispatch | `double` clause → `x := 10` | 3 |
| 2.4.2 | substitute | body `x * 2` → `10 * 2` | 3 |
| 2.4.3 | fold-prim | `10 * 2` → `20` | 3 |

**Reduced form:** `20` (literal). Counter 3. Zero residual calls.

## Call 3 — `N.helper(7)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 3.1 | dispatch | `N.helper` single clause `helper(x)` → bind `x := 7` | 1 |
| 3.2 | substitute | body `x + 100` → `7 + 100` | 1 |
| 3.3 | fold-prim | `7 + 100` → `107` | 1 |

**Reduced form:** `107` (literal). Counter 1.

## main, after reduction

```
fn main() do
  print(42)
  print(20)
  print(107)
end
```

All three module-qualified calls dissolved. **Zero bodies** emitted for
`M.double`, `M.quad`, `N.helper`. Only `main` and `print`'s extern
remain.

## Findings

**Modules add no new reducer-level concerns.** `M.double` and
`N.helper` are just fns with qualified names. Once name resolution
(parser/lowering) has resolved `M.double` to a specific `FnIr`, the
reducer operates exactly as in ast_eval. The module boundary is a
*lexical* feature, not an IR one.

**Whole-program / closed-world is what makes this clean.** Under the
"Scope of analysis" section of `bodies-are-boundaries.md`, the reducer
walks the call graph from roots (`main`, spawned fns). All three
qualified fns are reachable; nothing about them being in `M`/`N` vs.
the top level changes the walk. Separate compilation would require a
different model — but that's deferred per design.

**`M.quad(5)` exercises nested calls, not nested modules.** The
`double(double(x))` shape gives us a recurse step on a literal-int
argument. This is the "literal scalar countdown" case named in
`red-0`'s structural-decrease discussion — recursion into a known
literal qualifies as decrease because the value is statically
inspectable. Each inner call's input is a literal int, so dispatch +
substitute + fold-prim drives both layers to a single literal.

**Judgment call surfaced (minor):** the recurse rule is stated in
terms of "input Descr strictly structurally smaller than the parent's."
For `M.quad(5)`, the inner `double(5)` is not a recursive call into
the *same* fn — it's a fresh callsite inside `quad`'s reduced body.
Strictly the rule we want here is plain outside-in traversal, not
"recurse for structural decrease." The template treats them as the
same step ("counter +1"); this walk follows that convention. Naming
nit, not a hopeless issue.

**No module-level features fire.** This fixture has no `import`, no
`use`, no module attributes, no macros. The seven rules suffice.

**Spike outcome for this fixture: GO.** Predicted shape matches the
table in `bodies-are-boundaries.md` for fully-reduced fixtures:
**0 user bodies, 0 allocations.**
