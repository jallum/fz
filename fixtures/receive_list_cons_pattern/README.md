---
purpose: "receive with list cons / empty list / atom default — locks ListCons three-path parity"
paths: [jit, interp, aot]
budget.codegen.functions: 29
budget.codegen.instructions: 514
budget.specs.count: 17
budget.typer.worklist_pops: 38
budget.typer.walk_calls: 38
budget.typer.type_fn_calls: 17
budget.typer.matcher_specs: 0
budget.typer.vars: 74
budget.typer.blocks: 20
budget.typer.stmts: 30
budget.typer.dispatches: 7
---

# receive_list_cons_pattern

fz-puj.44 (X3) — receive matcher implementing SwitchKind::ListCons.

Three messages sent (a non-empty list, an empty list, an atom) and three
receives drain them in source order. Each clause set mixes `[h | _]`, `[]`,
and a wildcard default so the matrix specialises ListCons with three keys
(Cons → projects head via SubjectRef::ListHead; EmptyList; Nil-as-default).

Locks that interp/JIT/AOT all bind `h` to the list's first element, route
`[]` to the EmptyList arm, and fall through atoms to the wildcard.
