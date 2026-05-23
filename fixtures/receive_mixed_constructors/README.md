---
purpose: "selective receive whose clauses mix top-level constructors (atom + tuple + wildcard)"
paths: [jit, interp, aot]
budget.codegen.functions: 9
budget.codegen.instructions: 295
budget.specs.count: 5
budget.typer.worklist_pops: 8
budget.typer.walk_calls: 8
budget.typer.type_fn_calls: 5
budget.typer.matcher_specs: 0
budget.typer.vars: 27
budget.typer.blocks: 9
budget.typer.stmts: 14
budget.typer.dispatches: 1
---

# receive_mixed_constructors

fz-puj.37 (H8) — parity oracle for the receive shape where clauses dispatch
over different top-level constructors. The matrix builds a `Switch` whose
specialized cases cover the atom and tuple clauses, with the wildcard clause
forming a reachable default Leaf (not a Fail). Locks the AOT
`compile_pattern` shape that H9's compiled matcher fn must reproduce.
