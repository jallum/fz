---
purpose: "closing fixture of the destructure-up-through-quicksort arc — `{lo, hi} = partition(...)` on the hot path of a recursive sort"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 18
budget.codegen.instructions: 578
budget.specs.count: 18
budget.planner.worklist_pops: 110
budget.planner.walk_calls: 110
budget.planner.type_fn_calls: 28
budget.planner.matcher_specs: 0
budget.planner.vars: 69
budget.planner.blocks: 18
budget.planner.stmts: 43
budget.planner.dispatches: 13
---

# quicksort

The fixture that closes [[fz-fyq]]. Sorts `[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]`
via classic divide-and-conquer:

- `partition/4` splits the rest of the list around the pivot, returning a
  `{lo, hi}` tuple of the two sub-lists.
- `qsort/1` destructures that tuple — `{lo, hi} = partition(...)` — on
  the hot path of every recursive call.
- `append/2` glues the recursively-sorted halves back together.

This is the program destructuring exists for: a tuple-returning helper
whose two results need to flow into the next call, where without `=`-bind
you would either write nested calls (`f(snd(partition(...)), fst(...))`)
or build accessor helpers per arity. The fact that
`{lo, hi} = partition(p, rest, [], [])` is one line, irrefutable, and
folds to pure tuple projection in CLIF is the whole point.

## Notes

`append/2` is body-recursive — fine for the 11-element demo input, would
blow the stack on a million-element list. This fixture is a
feature-coverage smoke, not a perf benchmark; the tail-recursive
formulation is a worthwhile exercise but unrelated to what's being
proved here.

The `append`, `partition`, and `qsort` clauses all use the standard
empty-list plus cons-list split. The pattern checker proves that shape
exhaustive when the typed subject domain is known to be a list, so this
fixture is also a regression against spurious `type/no-matching-clause`
diagnostics on list-total helpers.

After printing the sorted list, this fixture prints
`Process.heap_alloc_stats/0` and a `heap_bytes` headline computed from
`:list_cons_bytes + :struct_bytes + :map_bytes`. The full map keeps runtime
path counters visible; the headline isolates immutable value heap objects from
frame and scheduler details.

Return-demand destination planning target for native JIT/AOT:

- `list_cons_allocs = 48`
- `list_cons_bytes = 768`
- `struct_allocs = 0`
- `struct_bytes = 0`
- `closure_allocs = 0`
- `closure_bytes = 0`
- `map_allocs = 0`
- `map_bytes = 0`
- `heap_bytes = 768`

Those numbers are the pinned return-demand result. JIT and AOT keep this
target; the interpreter and REPL remain direct IR baselines because they do not
execute native ReturnDemand lowering.
