# attributes — paper walk

Drives every top-level callsite in `main` through the seven reducer
rules (see [red-0-ast-eval-paper-walk.md](red-0-ast-eval-paper-walk.md)
for the rule table).

## The source

```
defmodule Greeter do
  @moduledoc "Hand-rolled greeter for the v1 demo."

  @doc "Returns a friendly greeting for the given name atom."
  fn hi(name), do: name

  @doc "Echoes its argument back."
  fn echo(x), do: x
end

fn main() do
  print(Greeter.hi(:alice))
  print(Greeter.echo(42))
end
```

Expected output:
```
:alice
42
```

The `@moduledoc` / `@doc` attributes are parse-only metadata; they
attach to module/function definitions and contribute nothing to the
IR or to reduction. The reducer never sees them.

## Call 1 — `print(Greeter.hi(:alice))`

`Greeter.hi/1` is a single-clause identity function: `fn hi(name),
do: name`.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | sole clause head `(name)` matches `atom_lit(:alice)`; bind `name := :alice` | 1 |
| 1.2 | substitute | body `name` → `:alice` | 1 |
| 1.3 | fold-prim | body is already a literal Descr; nothing to fold | 1 |
| 1.4 | stop-opaque | outer `print` is extern; leave in place with literal arg | 1 |

**Reduced form:** `print(:alice)`.

## Call 2 — `print(Greeter.echo(42))`

`Greeter.echo/1` is the same identity shape with a different name.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | sole clause head `(x)` matches `int_lit(42)`; bind `x := 42` | 1 |
| 2.2 | substitute | body `x` → `42` | 1 |
| 2.3 | stop-opaque | outer `print` is extern; leave in place | 1 |

**Reduced form:** `print(42)`.

## main, after reduction

```
fn main() do
  print(:alice)
  print(42)
end
```

Both `Greeter.hi` and `Greeter.echo` dissolve. Module-qualified names
(`Greeter.hi`) resolve at name-resolution time — the reducer sees a
plain `FnId` like any other.

## Findings

The walk is mechanical.

**Expected user-function body count:** 0. Both `Greeter.hi` and
`Greeter.echo` are identity functions reducible at their sole
callsites. `main` is always emitted; `print` is extern.

**Boundaries:** only `print` (twice).

**Feature surfaced — module attributes are reducer-transparent.**
`@moduledoc` and `@doc` are documentation metadata; they live on the
AST/module-info side and never reach IR. **Not a gap, but worth
noting:** the reducer only sees IR, so any attribute that *does*
matter for reduction (e.g. `@spec`, `@no_inline`) must be lifted onto
the FnIr / Module structure before the reducer pass runs. Today's
`@spec` plumbing already does this (per fz-ul4.31); future attributes
will need similar lifting.

**Feature surfaced — module-qualified call resolution.** `Greeter.hi`
is module-path syntax that resolves to a fully-qualified `FnId` before
the reducer runs. No new rule needed; just a reminder that name
resolution is upstream of reduction.

**Nothing to call out as a gap.**
