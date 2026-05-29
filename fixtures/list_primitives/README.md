---
purpose: "list primitives from scratch — length / reverse / map / foldl exercising cons-pattern dispatch and first-class fns"
paths: [jit, interp, aot, repl]
---

# list_primitives

List primitives from scratch — `length` / `reverse` / `map` / `foldl` exercising
cons-pattern clause dispatch and first-class functions, self-checked in-language:

```fz
assert(reverse(xs) == [5, 4, 3, 2, 1], "reverse via accumulator")
assert(map(double, xs) == [2, 4, 6, 8, 10], "map applies a first-class fn")
assert(foldl(add, 0, xs) == 15, "foldl sums via a first-class fn")
```

`reverse`/`foldl` are tail-recursive; `length`/`map` are body-recursive on
purpose to keep both shapes represented.
