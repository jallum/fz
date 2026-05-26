---
purpose: "source-level filter allocation baseline for guarded recursive list traversal"
paths: [jit, interp, aot, repl]
---

# filter_stats

Pins a first-order source-level filter shape:

```fz
fn filter_lt([], _), do: []
fn filter_lt([h | t], limit) when h < limit, do: [h | filter_lt(t, limit)]
fn filter_lt([_ | t], limit), do: filter_lt(t, limit)
```

Filtering `[1, 5, 2, 8, 3]` with limit `4` should allocate the five input
literal cons cells and three kept output cons cells. No tuple/struct or map
objects are needed for the value path.
