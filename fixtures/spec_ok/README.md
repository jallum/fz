---
purpose: "fz-ul4.31.6 — declared @spec matches inferred behavior;"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 3
budget.codegen.instructions: 21
budget.specs.count: 3
budget.planner.worklist_pops: 5
budget.planner.walk_calls: 5
budget.planner.type_fn_calls: 3
budget.planner.matcher_specs: 0
budget.planner.vars: 11
budget.planner.blocks: 4
budget.planner.stmts: 5
budget.planner.dispatches: 2
---

# spec_ok

fz-ul4.31.6 — declared @spec matches inferred behavior;

## Notes

         runs identically on interp, jit, aot
