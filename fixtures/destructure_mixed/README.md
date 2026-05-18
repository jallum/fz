---
purpose: "nested destructure mixing tuple arity and list cons — `{[h | t], y} = make()` across all four legs"
paths: [jit, interp, aot, repl]
---

# destructure_mixed

`{[h | t], y} = make()` — nested destructure binding through a tuple
into a list-cons in one leg of the tuple. Stresses the matrix
helpers' recursion (tuple specialization → list-cons specialization)
and confirms `BranchOrigin::PatternBind` propagates across both
levels so the diagnostic stays silent end-to-end.
