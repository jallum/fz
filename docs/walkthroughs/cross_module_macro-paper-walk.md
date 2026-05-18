# cross_module_macro — paper walk under the RED.0 reducer

Paper-only walk; rules per `red-0-ast-eval-paper-walk.md`.

Expected output: `42`.

## The source (pre-expansion)

```
defmodule Helpers do
  fn double(x), do: x * 2

  defmacro twice(x) do
    quote do: double(unquote(x))
  end
end

defmodule App do
  import Helpers, only: [twice: 1]

  fn run(n) do
    twice(n)
  end
end

fn main() do
  print(App.run(21))
end
```

`twice/1` is a **macro**, not a fn. Macros expand at parse / lower
time, not at reducer time. The reducer never sees `defmacro` or
`quote`/`unquote`; it sees the result of expanding every macro call
into its replacement IR.

## The source the reducer sees (post-expansion)

After macro expansion, the call `twice(n)` inside `App.run` is
replaced by the macro body with `unquote(x)` substituted by the
argument expression `n`. That yields `double(n)`, and since the macro
came from `Helpers` (imported into `App`), the unqualified `double`
resolves to `Helpers.double`.

The effective IR seen by the reducer:

```
fn Helpers.double(x), do: x * 2

fn App.run(n) do
  Helpers.double(n)
end

fn main() do
  print(App.run(21))
end
```

No trace of `twice/1` remains. No `quote`/`unquote` remains. The
macro is gone.

## Call 1 — `App.run(21)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | `App.run` single clause `run(n)` → `n := 21` | 1 |
| 1.2 | substitute | body `Helpers.double(n)` → `Helpers.double(21)` | 1 |
| 1.3 | recurse | reduce `Helpers.double(21)` | 2 |
| 1.3.1 | dispatch | `Helpers.double` clause `double(x)` → `x := 21` | 2 |
| 1.3.2 | substitute | body `x * 2` → `21 * 2` | 2 |
| 1.3.3 | fold-prim | `21 * 2` → `42` | 2 |

**Reduced form:** `42` (literal). Counter 2.

## main, after reduction

```
fn main() do
  print(42)
end
```

**Zero user bodies emitted.**

## Findings

**Macros are invisible to the reducer.** `defmacro twice` produces no
FnIr — it produces an expander that runs during front-end lowering.
By the time the IR exists, every `twice(...)` callsite has been
rewritten in place. The reducer sees only post-expansion IR. This is
the same contract Elixir, Rust, and Scheme give their later compiler
stages.

**Hygiene is a front-end property, not a reducer concern.** Whatever
name-capture / hygiene story the expander implements is settled before
the IR is built. The reducer assumes well-scoped IR with resolved
FnIds; macro expansion either produces that or fails earlier.

**`import` interacts with macros in the front-end, not here.** The
`import Helpers, only: [twice: 1]` directive permits the unqualified
`twice` reference inside `App.run` to resolve to the macro in
`Helpers`. Once `twice(n)` has been replaced by its expansion, the
generated `double(n)` likewise resolves through the same import-set
machinery to `Helpers.double`. All of that is settled before the
reducer runs.

**Predicted shape:** 0 user bodies, 0 allocations. Same as every
other fully-reduced fixture in this batch.

**Edge case worth naming:** if a macro expanded into IR that the
reducer's seven rules could not handle (e.g., new term shapes, quoted
fragments leaking through), that would surface as a hopeless issue.
For this fixture the expansion is a plain function call, so the rules
apply directly. **A general guarantee would be:** macro expansion must
produce IR within the reducer's grammar — i.e., expansion is total
into plain IR before the reducer runs. The fixture is consistent with
this guarantee; nothing in the file challenges it.

**Spike outcome for this fixture: GO.** No hopeless issue. Macros do
not extend the reducer rule set. The seven rules suffice on
post-expansion IR.
