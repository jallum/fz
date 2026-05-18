# import — paper walk under the RED.0 reducer

Paper-only walk; rules per `red-0-ast-eval-paper-walk.md`.

Expected output: `42`.

## The source

```
defmodule Math do
  fn add(x, y), do: x + y
  fn mul(x, y), do: x * y
end

defmodule User do
  import Math, only: [add: 2]

  fn calc(x, y), do: add(x, y)
end

fn main() do
  print(User.calc(10, 32))
end
```

Module structure: `Math` defines `add/2` and `mul/2`. `User` imports
only `add/2` from `Math` and defines `calc/2`. After name resolution,
the unqualified `add(x, y)` inside `User.calc` resolves to
`Math.add(x, y)`. The reducer sees three fns (`Math.add`, `Math.mul`,
`User.calc`) plus `main`. `Math.mul` is never called and is therefore
unreachable from any root.

## Call 1 — `User.calc(10, 32)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | `User.calc` single clause `calc(x, y)` → `x := 10`, `y := 32` | 1 |
| 1.2 | substitute | body `add(x, y)` → `Math.add(10, 32)` (import already resolved to fully-qualified callee at lower time) | 1 |
| 1.3 | recurse | reduce `Math.add(10, 32)` — outside-in traversal into the substituted callsite | 2 |
| 1.3.1 | dispatch | `Math.add` single clause → `x := 10`, `y := 32` | 2 |
| 1.3.2 | substitute | body `x + y` → `10 + 32` | 2 |
| 1.3.3 | fold-prim | `10 + 32` → `42` | 2 |

**Reduced form:** `42` (literal). Counter 2.

## main, after reduction

```
fn main() do
  print(42)
end
```

**Zero user bodies emitted.** `User.calc` and `Math.add` both dissolve.
`Math.mul` was never reachable and is pruned by the existing
reachable-specs walk (or never emitted in the first place since the
reducer is driven from roots).

## Findings

**`import` is a front-end symbol-resolution feature; the reducer
doesn't see it.** The `import Math, only: [add: 2]` directive changes
how names resolve inside `User`'s clauses during parsing/lowering.
Once the IR is built, every `Call` node already references a
fully-qualified FnId (`Math.add`). The reducer rules apply unchanged.

**Selective import (`only:`) is a parse-time filter; no IR effect.**
Whether the import names `add/2` only or imports everything, the
resolution-result inside `User.calc` is the same: `add(x, y)` →
`Math.add(x, y)`. The reducer doesn't observe the difference.

**`Math.mul` demonstrates the root-driven reachability story.** It's
defined but never called from a root. Per `bodies-are-boundaries.md`
§ "Scope of analysis," the reducer walks from roots; `Math.mul` is
unreachable and never has a body emitted. This is the existing
`reachable_specs` BFS (fz-ul4.42) doing its job — the reducer doesn't
need to add anything.

**No new judgment calls.** All steps are mechanical. Same conclusion
as `modules` and `nested_modules`: module-level features are
front-end concerns; the reducer sees post-resolution IR.

**Predicted shape:** 0 user bodies, 0 allocations.

**Spike outcome for this fixture: GO.** No hopeless issue. The seven
rules suffice without extension.
