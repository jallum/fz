---
purpose: "selective receive whose clauses mix top-level constructors (atom + tuple + wildcard)"
paths: [jit, interp, aot]
budget.codegen.functions: 8
budget.codegen.instructions: 121
budget.specs.count: 4
budget.typer.worklist_pops: 5
budget.typer.walk_calls: 5
budget.typer.type_fn_calls: 4
budget.typer.matcher_specs: 0
budget.typer.vars: 26
budget.typer.blocks: 8
budget.typer.stmts: 14
budget.typer.dispatches: 0
---

# receive_mixed_constructors

fz-puj.37 (H8) — parity oracle for the receive shape where clauses dispatch
over different top-level constructors. The matrix builds a `Switch` whose
specialized cases cover the atom and tuple clauses, with the wildcard clause
forming a reachable default Leaf (not a Fail). Locks the AOT
`compile_pattern` shape that H9's compiled matcher fn must reproduce.
