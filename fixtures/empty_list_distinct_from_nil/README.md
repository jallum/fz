---
purpose: "pin fz-s9y semantics — `nil` and `[]` print as distinct strings"
paths: [jit, aot, interp, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 15
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 10
budget.planner.blocks: 1
budget.planner.stmts: 9
budget.planner.dispatches: 0
---

# empty_list_distinct_from_nil

`nil` and `[]` share a bit pattern in older versions of fz; after fz-s9y
they are distinct runtime values. This fixture exercises that:

- `dbg(nil)` renders as `nil`.
- `dbg([])` renders as `[]`.
- `dbg([1, 2, 3])` renders as `[1, 2, 3]` — the list terminator is
  now the EMPTY_LIST sentinel, not the nil atom-like value.

If this fixture regresses, someone has re-conflated `nil` with `[]`.
