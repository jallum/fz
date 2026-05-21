---
purpose: "list primitives from scratch — length / reverse / map / foldl exercising cons-pattern dispatch and first-class fns"
paths: [jit, interp, aot]
---

# list_primitives

list primitives from scratch — `length`, `reverse`, `map`, `foldl`
exercising cons-pattern dispatch and first-class fns.

## Notes

First fixture to exercise the list path end-to-end. Lists, list
literals, and `[h | t]` cons patterns are all in the parser/AST and
the runtime has list rendering and cons-cell allocation, but until
now no fixture combined them.

Covered:

- Cons-pattern dispatch in fn heads, alongside the `[]` base case.
- `[h | acc]` cons-construction in expression position.
- First-class fns passed in (`map`, `foldl`) and called against each
  element.
- `reverse` is tail-recursive via `reverse_acc/2`; `foldl/3` is
  tail-recursive directly. `length` and `map` are body-recursive on
  purpose to keep both shapes represented.

Output is four lines: `5`, `[5, 4, 3, 2, 1]`, `[2, 4, 6, 8, 10]`,
`15`.

Listed under `[jit, interp]` only; AOT can be added once a separate
pass confirms cons cells survive the AOT heap path.
