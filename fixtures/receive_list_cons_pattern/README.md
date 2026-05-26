---
purpose: "receive with list cons / empty list / atom default — locks ListCons three-path parity"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 20
budget.codegen.instructions: 572
budget.specs.count: 17
budget.planner.worklist_pops: 38
budget.planner.walk_calls: 38
budget.planner.type_fn_calls: 17
budget.planner.matcher_specs: 0
budget.planner.vars: 74
budget.planner.blocks: 20
budget.planner.stmts: 30
budget.planner.dispatches: 7
---

# receive_list_cons_pattern

fz-puj.44 (X3) — receive matcher implementing SwitchKind::ListCons.

Three messages sent (a non-empty list, an empty list, an atom) and three
receives drain them in source order. Each clause set mixes `[h | _]`, `[]`,
and a wildcard default so the matrix specialises ListCons with three keys
(Cons → projects head via SubjectRef::ListHead; EmptyList; Nil-as-default).

Locks that interp/JIT/AOT all bind `h` to the list's first element, route
`[]` to the EmptyList arm, and fall through atoms to the wildcard.
