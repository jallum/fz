---
purpose: "closing fixture of the destructure-up-through-quicksort arc — `{lo, hi} = partition(...)` on the hot path of a recursive sort"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 17
budget.codegen.instructions: 1574
budget.specs.count: 17
budget.typer.worklist_pops: 78
budget.typer.walk_calls: 78
budget.typer.type_fn_calls: 27
budget.typer.matcher_specs: 0
budget.typer.vars: 141
budget.typer.blocks: 47
budget.typer.stmts: 68
budget.typer.dispatches: 25
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
