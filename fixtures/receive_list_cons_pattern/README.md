---
purpose: "receive with list cons / empty list / atom default — locks ListCons three-path parity"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 20
budget.codegen.instructions: 534
budget.specs.count: 17
budget.planner.worklist_pops: 42
budget.planner.walk_calls: 42
budget.planner.type_fn_calls: 17
budget.planner.matcher_specs: 0
budget.planner.vars: 68
budget.planner.blocks: 17
budget.planner.stmts: 27
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
