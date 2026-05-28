---
purpose: "source-level append allocation baseline proves ordinary list append needs no append BIF"
paths: [jit, interp, aot, repl]
---

# append

Pins source-level `append/2` as an ordinary recursive function:

```fz
fn append([], ys), do: ys
fn append([h | t], ys), do: [h | append(t, ys)]
```

The program appends `[1, 2, 3]` to `[4, 5]`, prints the result, snapshots
current-process heap allocation counters, and prints the list/struct/map heap
headline.

Target for native JIT/AOT:

- the two list literals allocate five cons cells;
- owned-cons reuse removes the append prefix copy, so no extra cons cells are
  allocated;
- no tuple/struct or map objects are needed for the value path;
- `heap_bytes = 80`.

This fixture is deliberately not an append BIF test. The accompanying dump
assertion proves that `append` remains a source function in the typed specs and
native CLIF.
