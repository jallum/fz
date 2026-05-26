---
purpose: "source-level tuple-tree traversal allocation baseline"
paths: [jit, interp, aot, repl]
---

# tree_stats

Pins a tuple-shaped tree traversal using ordinary source functions and tuple
patterns:

```fz
fn inc_tree(:empty), do: :empty
fn inc_tree({:node, left, value, right}), do: {:node, inc_tree(left), value + 1, inc_tree(right)}
```

The input tree has three `{:node, left, value, right}` tuples. Native JIT/AOT
currently fold the literal input tree into the traversal and allocate only the
three rebuilt output nodes. The interpreter/REPL direct IR path allocates both
the three input nodes and the three output nodes. No list or map allocations are
needed in either path.
