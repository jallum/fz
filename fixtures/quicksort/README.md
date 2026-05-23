---
purpose: "closing fixture of the destructure-up-through-quicksort arc — `{lo, hi} = partition(...)` on the hot path of a recursive sort"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 13
budget.codegen.instructions: 361
budget.specs.count: 13
budget.typer.worklist_pops: 75
budget.typer.walk_calls: 75
budget.typer.type_fn_calls: 23
budget.typer.matcher_specs: 0
budget.typer.vars: 125
budget.typer.blocks: 43
budget.typer.stmts: 72
budget.typer.dispatches: 21
---

# quicksort

The fixture that closes [[fz-fyq]]. Sorts `[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]`
via classic divide-and-conquer:

- `partition/4` splits the rest of the list around the pivot. It uses one
  guarded cons clause for values below the pivot and one fallback cons
  clause for the high side, then returns a `{lo, hi}` tuple.
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
empty-list plus cons-list split. `partition/4` also puts the pivot
comparison in the clause guard (`when h < p`), so the function reads as
three declarative cases: done, low side, high side. The pattern checker
allows guards to decline a match without making the source invalid, so the
unguarded fallback cons clause is the coverage witness for the high side.
