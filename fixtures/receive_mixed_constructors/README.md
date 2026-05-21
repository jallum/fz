---
purpose: "selective receive whose clauses mix top-level constructors (atom + tuple + wildcard)"
paths: [jit, interp, aot]
---

# receive_mixed_constructors

fz-puj.37 (H8) — parity oracle for the receive shape where clauses dispatch
over different top-level constructors. The matrix builds a `Switch` whose
specialized cases cover the atom and tuple clauses, with the wildcard clause
forming a reachable default Leaf (not a Fail). Locks the AOT
`compile_pattern` shape that H9's compiled matcher fn must reproduce.
