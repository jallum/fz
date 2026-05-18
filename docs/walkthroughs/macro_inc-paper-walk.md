# macro_inc — paper walk

Drives every top-level callsite in `main` through the seven reducer
rules (see [red-0-ast-eval-paper-walk.md](red-0-ast-eval-paper-walk.md)
for the rule table).

## The source

```
defmacro inc(x) do
  quote do: unquote(x) + 1
end

defmacro double(x) do
  quote do: unquote(x) * 2
end

fn main() do
  print(inc(41))
  print(double(21))
  print(inc(double(20)))
end
```

Expected output:
```
42
42
41
```

## The key observation: macros expand pre-IR

`defmacro` / `quote` / `unquote` are **compile-time AST rewrites**
that run during macro-expansion, *before* IR generation. The reducer
never sees `inc` or `double` as functions — by the time the reducer
runs, `main` has already been rewritten to:

```
fn main() do
  print(41 + 1)
  print(21 * 2)
  print((20 * 2) + 1)
end
```

That's what the reducer sees. From here the walk is the same as
`vr1_int_arith`.

## Call 1 — `print(41 + 1)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | fold-prim | `41 + 1` → `int_lit(42)` | 1 |
| 1.2 | stop-opaque | `print` extern; leave in place | 1 |

## Call 2 — `print(21 * 2)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | fold-prim | `21 * 2` → `int_lit(42)` | 1 |
| 2.2 | stop-opaque | `print` extern; leave in place | 1 |

## Call 3 — `print((20 * 2) + 1)`

Two nested Prims, both with literal inputs.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 3.1 | fold-prim | inner `20 * 2` → `int_lit(40)` | 1 |
| 3.2 | fold-prim | outer `40 + 1` → `int_lit(41)` | 2 |
| 3.3 | stop-opaque | `print` extern; leave in place | 2 |

## main, after reduction

```
fn main() do
  print(42)
  print(42)
  print(41)
end
```

## Findings

The walk is mechanical *because the macros expanded upstream*.

**Expected user-function body count:** 0. No user functions exist in
the post-expansion IR. `main` is always emitted; `print` is extern.

**Boundaries:** only `print` (three times).

**Feature surfaced — `defmacro` / `quote` / `unquote` are NOT a
reducer concern.** They are AST → AST transformations that happen
during macro expansion, before the AST → IR lowering. The reducer
operates on IR; by then the macros have been spliced in. The reducer
needs no new rule for macros.

**Subtlety to flag for the design.** *If* fz ever adds a "runtime
macro" or a macro that can't fully expand at compile time (e.g.
depending on a runtime value), this story changes. Today's
`defmacro` does not, and the design doc doesn't mention any such
extension. **Not a gap; a precondition to record:** the reducer
assumes all macros are fully expanded by the time it runs.

**Subtlety to flag for goldens.** Macro expansion may introduce
hygienic renames (`x` inside a quote → a gensym). The reducer's
`substitute` rule must handle gensym'd binders the same as
user-written ones (it should — they're just bound names in IR). Worth
verifying in RED.6 that macro-using fixtures' goldens are unaffected
by reduction beyond the literal-arithmetic collapse.
