---
purpose: "source-level reverse allocation baseline for accumulator-style list traversal"
paths: [jit, interp, aot, repl]
---

# reverse_stats

Pins ordinary source-level `reverse/1` and `reverse_into/2` as an
accumulator-style list traversal. Reversing a five-element list should allocate
the five input literal cons cells and five output cons cells. No tuple/struct or
map objects are needed for the value path.
