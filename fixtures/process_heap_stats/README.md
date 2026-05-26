---
purpose: "Process.heap_alloc_stats/0 exposes deterministic current-process heap allocation counters as ordinary runtime output"
paths: [jit, interp, aot, repl]
---

# process_heap_stats

Pins the basic `Process.heap_alloc_stats/0` runtime API. The program allocates
two list cons cells, snapshots the current process allocation counters, and
prints the returned map.

The expected output pins the full map shape and proves snapshot-first
semantics: `:map_allocs` is `0` because the stats map is allocated only after
the snapshot is taken.
