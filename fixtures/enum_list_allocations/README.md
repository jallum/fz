---
purpose: "runtime Enum list functions preserve the minimum native list-cons allocation floor"
paths: [jit, interp, aot, repl]
---

# enum_list_allocations

Pins the runtime-library list path for the non-building Enum functions:

```fz
Enum.count(xs)
Enum.member?(xs, 3)
Enum.reduce(xs, {:cont, 0}, fn (x, acc) -> {:cont, acc + x})
```

The program builds one five-element input list, runs those functions through
the runtime `Enum` and `Enumerable` modules, snapshots current-process heap
allocation counters, and prints the list/struct/map heap headline.

Target for native JIT/AOT:

- the input list literal allocates five cons cells;
- `Enum.count/1`, `Enum.member?/2`, and `Enum.reduce/3` allocate no additional
  cons cells while walking that list;
- no map objects are needed before the stats snapshot;
- `list_cons_allocs = 5`;
- `list_cons_bytes = 80`.

This fixture deliberately excludes `Enum.sort/1`. The current runtime sort is
a source-level merge sort that builds split/reverse/merge work lists, so it has
a different allocation contract from the list-consuming functions pinned here.
