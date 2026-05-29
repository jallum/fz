---
purpose: "nested destructure mixing tuple arity and list cons — `{[h | t], y} = make()` across all four legs"
paths: [jit, interp, aot, repl]
---

# destructure_mixed

`{[h | t], y} = make()` — nested destructure binding through a tuple into a
list-cons in one leg of the tuple. Stresses the matrix helpers' recursion
(tuple specialization → list-cons specialization) and confirms
`BranchOrigin::PatternBind` propagates across both levels. Self-checked
in-language:

```fz
{[h | t], y} = make()
assert(h == 1, "nested cons head binds through the tuple")
assert(t == [2, 3], "nested cons tail binds through the tuple")
assert(y == 99, "second tuple leg binds")
```
