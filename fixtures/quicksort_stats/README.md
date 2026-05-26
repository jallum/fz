---
purpose: "quicksort allocation baseline — pins runtime heap bytes requested for list, tuple/struct, and map objects"
paths: [jit, interp, aot, repl]
---

# quicksort_stats

Runs the same 11-element quicksort program as `fixtures/quicksort`, then prints
the full `Process.heap_alloc_stats/0` map. This fixture is the runtime
allocation baseline for destination-passing work.

The final `heap_bytes` line is the sum of `:list_cons_bytes`, `:struct_bytes`,
and `:map_bytes`. The full map keeps every runtime counter visible; the
headline line keeps the destination-passing comparison focused on immutable
value heap objects while leaving frame and scheduler runtime details out of the
headline number.

This fixture uses path-specific stdout goldens because closure and scalar-box
counters are runtime-path facts: JIT, interpreter, AOT, and REPL all agree on
list/struct/map allocation for the sorted value, while scheduler closure
allocation legitimately differs by execution path.

Return-demand destination passing target:

- `list_cons_allocs = 48`
- `list_cons_bytes = 768`
- `struct_allocs = 0`
- `struct_bytes = 0`
- `map_allocs = 0`
- `map_bytes = 0`
- `heap_bytes = 768`

Those numbers are the expected steady-state goal for the return-demand arc. The
current goldens remain the measured baseline until the compiler can select
TupleFields and ListTail return-demand capabilities.
