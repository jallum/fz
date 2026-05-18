# list_primitives — paper walk

Fixture: `fixtures/list_primitives/input.fz`. Expected output: `5`,
`[5, 4, 3, 2, 1]`, `[2, 4, 6, 8, 10]`, `15`.

This walkthrough drives every callsite in `main` through the reducer
rules by hand. This is the longest walk in the batch: a 5-element
list traversed by four different list-recursive functions, two of
which (`map`, `foldl`) take a function argument. For brevity, we
show the first 1-2 steps of each traversal in full, then summarize
the recursive shape with "..." and show the final step.

## The source

```
fn length([]), do: 0
fn length([_ | t]), do: 1 + length(t)

fn reverse(xs), do: reverse_acc(xs, [])
fn reverse_acc([], acc), do: acc
fn reverse_acc([h | t], acc), do: reverse_acc(t, [h | acc])

fn map(_, []), do: []
fn map(f, [h | t]), do: [f(h) | map(f, t)]

fn foldl(_, acc, []), do: acc
fn foldl(f, acc, [h | t]), do: foldl(f, f(acc, h), t)

fn double(x), do: x * 2
fn add(a, b), do: a + b

fn main() do
  xs = [1, 2, 3, 4, 5]
  print(length(xs))
  print(reverse(xs))
  print(map(double, xs))
  print(foldl(add, 0, xs))
end
```

`xs` is a fully-static list — a chain of `cons(1, cons(2, cons(3,
cons(4, cons(5, [])))))`. Its Descr is a literal list of length 5
with literal int elements. Pattern dispatch can statically select
clauses at every step.

**Structural-decrease note.** Each recursive call passes the tail of
the input list, which is a projection of the input cons cell. List
tails are strictly smaller in the structural measure (template § on
structural-decrease names list head/tail projections explicitly). So
`recurse` fires at every step.

## Call 1 — `length(xs)` = `length([1, 2, 3, 4, 5])`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | clause 0 `[]` rejects (input non-empty); clause 1 `[_ | t]` matches → bind `t := [2, 3, 4, 5]` | 1 |
| 1.2 | substitute | body `1 + length(t)` → `1 + length([2, 3, 4, 5])` | 1 |
| 1.3 | recurse | input is the literal tail (strictly smaller; list length 4 < 5) → reduce `length([2, 3, 4, 5])` | 2 |
| 1.3.1 | dispatch | clause 1 matches → `t := [3, 4, 5]` | 2 |
| 1.3.2 | substitute + recurse | → `1 + length([3, 4, 5])` (recurse, list length 3) | 3 |
| ... | ... | each step reduces the cons head, recurses on tail; depth shrinks by 1 each time | ... |
| 1.6 | recurse | reduce `length([5])` (length 1) | 5 |
| 1.6.1 | dispatch | clause 1 → `t := []` | 5 |
| 1.6.2 | substitute + recurse | → `1 + length([])` (recurse, length 0) | 6 |
| 1.7 | dispatch | clause 0 `[]` matches → no bindings | 6 |
| 1.8 | substitute | body `0` → `0` | 6 |
| 1.9 | fold-prim | walk back up: `1 + 0` → `1`, `1 + 1` → `2`, ..., `1 + 4` → `5` (five fold-prim steps) | 6 |

**Reduced form:** `5`. Counter peaked at 6 — well under budget.

## Call 2 — `reverse(xs)` = `reverse([1, 2, 3, 4, 5])`

`reverse` is a one-clause indirection to `reverse_acc/2`.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | `reverse` single clause → bind `xs := [1, 2, 3, 4, 5]` | 1 |
| 2.2 | substitute | body → `reverse_acc([1, 2, 3, 4, 5], [])` | 1 |
| 2.3 | recurse | reduce `reverse_acc([1,2,3,4,5], [])` (note A on decrease) | 2 |
| 2.3.1 | dispatch | clause 0 `[]` rejects; clause 1 `[h | t]` matches → `h := 1`, `t := [2, 3, 4, 5]`, `acc := []` | 2 |
| 2.3.2 | substitute | body → `reverse_acc([2,3,4,5], [1 | []])` = `reverse_acc([2,3,4,5], [1])` (cons-literal construction is fold-prim on cons; see note B) | 2 |
| 2.3.3 | recurse | tail is strictly smaller → reduce `reverse_acc([2,3,4,5], [1])` | 3 |
| ... | ... | each step: peel head off first list, cons onto second; pattern same as 2.3.1–3 | ... |
| 2.7 | recurse | reduce `reverse_acc([5], [4, 3, 2, 1])` | 7 |
| 2.7.1 | dispatch | clause 1 → `h := 5`, `t := []`, `acc := [4, 3, 2, 1]` | 7 |
| 2.7.2 | substitute | → `reverse_acc([], [5, 4, 3, 2, 1])` | 7 |
| 2.7.3 | recurse | reduce `reverse_acc([], [5, 4, 3, 2, 1])` | 8 |
| 2.7.4 | dispatch | clause 0 `[]` matches → bind `acc := [5, 4, 3, 2, 1]` | 8 |
| 2.7.5 | substitute | body `acc` → `[5, 4, 3, 2, 1]` | 8 |

**Reduced form:** `[5, 4, 3, 2, 1]`. Counter peaked at 8.

**Note A — decrease for two-arg recursion.** `reverse_acc(t, [h |
acc])` — the *first* argument `t` is structurally smaller than the
input's first arg `[h|t]`. The *second* argument grew, but
structural-decrease only requires *some* projection witnesses a
strictly smaller measure. By convention (template § structural-
decrease) we measure on the recursing list. The accumulator's growth
is fine.

**Note B — cons construction folds.** `[h | acc]` where `h` and
`acc` are literal Descrs is a `Prim::Cons` (or equivalent) with
literal inputs. Fold-prim emits a literal cons Descr. Same shape as
the closure_lit case in `closure_typed_captures`: the literal-Descr
lattice has to admit literal lists. The IR already represents
literal cons cells in Descrs.

## Call 3 — `map(double, xs)` = `map(closure_lit(double, []), [1, 2, 3, 4, 5])`

The interesting case: a recursive list traversal with a fn argument.
At each cons cell, the reducer must inline `f(h)` where `f` is the
literal closure_lit and `h` is a literal int.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 3.1 | dispatch | clause 0 rejects (list non-empty); clause 1 `(f, [h|t])` matches → `f := closure_lit(double, [])`, `h := 1`, `t := [2, 3, 4, 5]` | 1 |
| 3.2 | substitute | body `[f(h) | map(f, t)]` → `[closure_lit(double, [])(1) | map(closure_lit(double, []), [2, 3, 4, 5])]` | 1 |
| 3.3 | recurse + closure-inline | inner `f(h)`: closure-inline (see Findings) → `double(1)` | 2 |
| 3.3.1 | dispatch | `double` clause → `x := 1` | 2 |
| 3.3.2 | substitute + fold-prim | `x * 2` → `1 * 2` → `2` | 2 |
| 3.4 | recurse | reduce `map(closure_lit(double, []), [2, 3, 4, 5])` — list arg is strictly smaller | 3 |
| 3.4.* | dispatch + substitute + closure-inline + fold-prim | repeat shape of 3.1–3.3 with `h := 2`, gives head `4`; recurse on `[3, 4, 5]` | 4 |
| ... | ... | continues for `h := 3` (→ `6`), `h := 4` (→ `8`), `h := 5` (→ `10`) | ... |
| 3.8 | recurse | reduce `map(closure_lit(double, []), [])` | 8 |
| 3.8.1 | dispatch | clause 0 `(_, [])` matches → bind `f := closure_lit(double, [])` (wildcard); empty list | 8 |
| 3.8.2 | substitute | body `[]` → `[]` | 8 |
| 3.9 | fold-prim | walk back up the cons constructions: `[10 | []]` → `[10]`, `[8 | [10]]` → `[8, 10]`, ..., `[2 | [4, 6, 8, 10]]` → `[2, 4, 6, 8, 10]` | 8 |

**Reduced form:** `[2, 4, 6, 8, 10]`. Counter peaked at 8.

**Key observation.** The reducer threads the closure_lit through
every recursive call to `map`. Because the closure_lit Descr is
literal and identical at every cell, `closure-inline + dispatch` on
`double` fires fresh at each cell. No `double` body is emitted; no
`map` body is emitted; no closure heap object is ever materialized.

## Call 4 — `foldl(add, 0, xs)` = `foldl(closure_lit(add, []), 0, [1, 2, 3, 4, 5])`

Tail-recursive accumulator. `f(acc, h)` is the inlined `add(acc,
h)` at each step.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 4.1 | dispatch | clause 1 matches → `f := closure_lit(add, [])`, `acc := 0`, `h := 1`, `t := [2,3,4,5]` | 1 |
| 4.2 | substitute | body → `foldl(closure_lit(add, []), f(0, 1), [2,3,4,5])` | 1 |
| 4.3 | recurse + closure-inline | inner `f(0, 1)`: closure-inline → `add(0, 1)` | 2 |
| 4.3.1 | dispatch + substitute + fold-prim | `add` clause; `a + b` → `0 + 1` → `1` | 2 |
| 4.4 | recurse | reduce `foldl(closure_lit(add, []), 1, [2,3,4,5])` — list arg strictly smaller | 3 |
| ... | ... | each step: inline `add(acc, h)`, fold to new acc, recurse on tail. accs go `0, 1, 3, 6, 10, 15` | ... |
| 4.8 | recurse | reduce `foldl(closure_lit(add, []), 15, [])` | 8 |
| 4.8.1 | dispatch | clause 0 `(_, acc, [])` matches → bind `acc := 15` | 8 |
| 4.8.2 | substitute | body `acc` → `15` | 8 |

**Reduced form:** `15`. Counter peaked at 8.

## main, after reduction

```
fn main() do
  print(5)
  print([5, 4, 3, 2, 1])
  print([2, 4, 6, 8, 10])
  print(15)
end
```

Zero user-fn bodies. Zero heap allocations at runtime — the literal
lists are constant data the print runtime can consume directly (or
unroll into per-element prints, depending on `print`'s lowering).

## Structural-decrease check, in detail

Every recursive call in this fixture has the shape `f(tail, ...)`
where `tail` is the cons-tail projection of the input's first list
argument. List-tail is named in the template as a structural
projection. The recurse rule fires at every step. The list of length
5 unrolls completely in ≤ 8 counter ticks per traversal — well under
the 32-step budget.

**This is the same kind of decrease as ast_eval's tuple-field
projection.** Both are "extract a sub-Descr by pattern projection."
The reducer doesn't need separate decreasers for tuples vs. lists —
both are forms of structural projection.

## Findings

**The walk is mechanical end-to-end** — once we accept the
closure-inline sub-rule introduced in `higher_order` and the
literal-cons fold introduced in `reverse` (Note B above).

**Three sub-rules / clarifications surface from this fixture:**

1. **closure-inline** (the 8th rule discussed in earlier
   walkthroughs): used at every cell of `map` and `foldl` to inline
   `f(h)` or `f(acc, h)` through a literal closure_lit callee.
2. **fold-prim on cons construction.** `[literal_head | literal_tail]`
   must fold to a literal cons Descr; otherwise the recursive
   reconstruction of lists in `length`, `reverse`, `map` blows the
   budget by leaving residual cons-allocations between each fold-up
   step. This is symmetric to fold-prim on `MakeClosure`: the literal
   lattice must include literal lists.
3. **fold-prim on cons destruction is implicit in dispatch.** When
   the input is a literal cons, dispatch on `[h | t]` binds `h` and
   `t` to literal sub-Descrs. The "decrease" is the same projection.

**Walk is long but uniform.** Five 5-element traversals of essentially
the same shape. The counter stays below 8 in every call — the
budget of 32 is generous for any practical list-with-literal-elements
fixture.

**What happens if the list were opaque?** If `xs` came from a
`receive` or an extern, the input Descr would be a wide list type;
`dispatch` on `[]` vs. `[h | t]` would fire `stop-opaque`. A body
for `length` (and `map`, etc.) would be emitted. The closure_lit
passed to `map` is still literal, so the body would be specialized
to "map-with-double inlined per cell" — one body, no `f` parameter.
This matches the user_b case in the design doc.

**Closures stored in lists / passed via runtime values are NOT
exercised here.** Every closure in this fixture is a zero-capture
`closure_lit(F, [])` originating at a top-level fn name. Lists of
opaque closures or closures-as-runtime-values are flagged in the
prompt as a likely-surprise category; they don't appear in
list_primitives.

**Predicted shape:** 0 user bodies, 0 allocations on the static-list
path. Matches the design-doc table ("list_primitives (static list):
0 bodies, none"). Boundary-body cases (opaque list) are tabled
separately in the design doc and are not paper-walked here.
