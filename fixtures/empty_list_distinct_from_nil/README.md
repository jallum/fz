---
purpose: "pin fz-s9y semantics — `nil` and `[]` print as distinct strings"
paths: [jit, aot, interp, repl]
budget.codegen.functions: 2
budget.codegen.instructions: 34
budget.specs.count: 2
budget.typer.worklist_pops: 3
budget.typer.walk_calls: 3
budget.typer.type_fn_calls: 2
budget.typer.matcher_specs: 0
budget.typer.vars: 28
budget.typer.blocks: 5
budget.typer.stmts: 12
budget.typer.dispatches: 1
---

# empty_list_distinct_from_nil

`nil` and `[]` share a bit pattern in older versions of fz; after fz-s9y
they are distinct runtime values. This fixture exercises that:

- `print(nil)` renders as `nil`.
- `print([])` renders as `[]`.
- `print([1, 2, 3])` renders as `[1, 2, 3]` — the list terminator is
  now the EMPTY_LIST sentinel, not the nil atom-like value.

If this fixture regresses, someone has re-conflated `nil` with `[]`.
