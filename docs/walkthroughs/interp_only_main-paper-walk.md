# interp_only_main — paper walk under the proposed reducer

## The reducer rules

See `red-0-ast-eval-paper-walk.md`.

## The source

```
fn inc(n) do n + 1 end
fn main(), do: print(inc(41))
```

Expected output: `42`.

## Program roots

Only `main` (no spawn).

## Root: `main`

```
fn main() do print(inc(41)) end
```

| Step | Rule | Detail |
|---|---|---|
| 1 | dispatch | `inc(41)` — one clause, head `(n)`. Binds `n := int_lit(41)`. |
| 2 | substitute | body becomes `int_lit(41) + 1`. |
| 3 | fold-prim | both inputs literal → `int_lit(42)`. |
| 4 | extern | `print(42)` — extern, leave in place. |

**Reduced main:** `print(42)`. The `inc` call dissolved.

## Bodies emitted

| Fn | Bodies |
|---|---|
| `main` | 1 |
| `inc` | **0** |

## Findings

**Textbook RED.3-class reduction.** Single-clause inlining with all
inputs literal. The simplest non-trivial case after `ast_eval`.

**"interp_only" is a name from the historical tier-0 era.** Per
README, this was a smoke test from the days when interp was tier 0.
The reducer is **path-agnostic** — Module → Module before the
backend split. Interp, JIT, and AOT all consume the same reduced
Module. The fixture's `paths` list (`jit, interp, repl`) is a runtime
concern, not a reducer concern.

**No judgment calls.** Trivial mechanical walk.
