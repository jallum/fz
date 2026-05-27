---
purpose: "nested destructure mixing tuple arity and list cons — `{[h | t], y} = make()` across all four legs"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 31
budget.specs.count: 2
budget.planner.worklist_pops: 3
budget.planner.walk_calls: 3
budget.planner.type_fn_calls: 2
budget.planner.matcher_specs: 0
budget.planner.vars: 34
budget.planner.blocks: 7
budget.planner.stmts: 18
budget.planner.dispatches: 1
---

# destructure_mixed

`{[h | t], y} = make()` — nested destructure binding through a tuple
into a list-cons in one leg of the tuple. Stresses the matrix
helpers' recursion (tuple specialization → list-cons specialization)
and confirms `BranchOrigin::PatternBind` propagates across both
levels so the diagnostic stays silent end-to-end.
