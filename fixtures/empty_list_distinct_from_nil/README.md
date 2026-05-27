---
purpose: "pin fz-s9y semantics — `nil` and `[]` print as distinct strings"
paths: [jit, aot, interp, repl]
budget.codegen.functions: 2
budget.codegen.instructions: 19
budget.specs.count: 2
budget.planner.worklist_pops: 3
budget.planner.walk_calls: 3
budget.planner.type_fn_calls: 2
budget.planner.matcher_specs: 0
budget.planner.vars: 28
budget.planner.blocks: 5
budget.planner.stmts: 12
budget.planner.dispatches: 1
---

# empty_list_distinct_from_nil

`nil` and `[]` share a bit pattern in older versions of fz; after fz-s9y
they are distinct runtime values. This fixture exercises that:

- `print(nil)` renders as `nil`.
- `print([])` renders as `[]`.
- `print([1, 2, 3])` renders as `[1, 2, 3]` — the list terminator is
  now the EMPTY_LIST sentinel, not the nil atom-like value.

If this fixture regresses, someone has re-conflated `nil` with `[]`.
