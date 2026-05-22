---
purpose: "receive with list cons / empty list / atom default — locks ListCons three-path parity"
paths: [jit, interp, aot]
budget.codegen.min_functions: 27
budget.codegen.max_functions: 27
budget.codegen.min_instructions: 500
budget.codegen.max_instructions: 752
budget.specs.min_count: 29
budget.specs.max_count: 44
---

# receive_list_cons_pattern

fz-puj.44 (X3) — receive matcher implementing SwitchKind::ListCons.

Three messages sent (a non-empty list, an empty list, an atom) and three
receives drain them in source order. Each clause set mixes `[h | _]`, `[]`,
and a wildcard default so the matrix specialises ListCons with three keys
(Cons → projects head via SubjectRef::ListHead; EmptyList; Nil-as-default).

Locks that interp/JIT/AOT all bind `h` to the list's first element, route
`[]` to the EmptyList arm, and fall through atoms to the wildcard.
