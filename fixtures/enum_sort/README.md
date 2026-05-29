---
purpose: "runtime-library Enum.sort (merge sort) allocation contract across four paths; pins JIT/AOT parity and the merge-step continuation-closure floor"
paths: [jit, interp, aot, repl]
---

# enum_sort

Sorts the same eleven-element list as [[quicksort]] — `[3, 1, 4, 1, 5, 9, 2,
6, 5, 3, 5]` — but through the runtime library's `Enum.sort/1` (a merge sort
in `src/modules/runtime_library/enum.fz`) instead of a hand-written quicksort.
Same input, same `dbg(stats)` shape, so the two fixtures are a direct
allocation contrast between a general-purpose stdlib sort and code the
destination planner fully optimizes.

```fz
sorted = Enum.sort([3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5])
```

After printing the sorted list, the fixture prints `Process.heap_alloc_stats/0`
and a `heap_bytes` headline (`:list_cons_bytes + :struct_bytes + :map_bytes`),
exactly as `quicksort` does.

## What it pins

**Native (JIT and AOT) produce byte-identical stats.** This is the regression
guard for [[fz-mt0]]: the JIT used to run on a flat 64 KiB heap while AOT and
the scheduler used the growable starter heap, so the two backends reported
different yield and closure counts for the same program. They must now agree.

Native floor:

- `list_cons_allocs = 61`
- `closure_allocs = 53` — see the decomposition below
- `scalar_box_allocs = 0`
- `heap_bytes = 976`
- `allocation_pressure_yields = 2`

The interpreter and REPL legs are direct-IR baselines: they do not run native
`ReturnDemand` / owned-cons-reuse lowering, so they allocate more cons cells
(`154`) and only the single comparator closure. They share the same growable
heap, so they take the same `2` allocation-pressure yields.

## The closure count improved, but is not zero

Where the hand-written quicksort lowers to **0** continuation closures (its
`append`/`qsort` non-tail recursion gets `ListTail` destination planning),
`Enum.sort` still allocates 53 closures. That is a real improvement over the
old native floor (`80` closures, `80` cons cells, `27` scalar boxes, and `1280`
heap headline bytes), but it is not the fully closure-free merge-sort shape.
Callable capabilities now let the planner see farther through the runtime
library boundary, so known reducer/comparator values stop carrying as much
dead callable state through native frames.

The remaining closures come from merge sort's non-tail recursion in `enum.fz`:
`merge_sort_lists` builds `[head | merge_sort_lists(...)]` inside a guarded
`if`, and the sort still has recursive structure that destination planning does
not fully flatten into the quicksort-style owned-cons path.

Further reducing the native count is future optimizer work. This fixture pins
the current post-capability contract so that any change in either direction
shows up loudly.
