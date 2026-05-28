---
purpose: "sequential calls returning tuple-pattern results (fz-i82 regression)"
paths: [interp, jit, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 22
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 31
budget.planner.blocks: 1
budget.planner.stmts: 24
budget.planner.dispatches: 0
---

# case_tuple_pattern_sequential

Regression lock for fz-i82. Two helpers — one `case`-based, one
`with`-based — each with a tuple-pattern arm and an atom-literal
fallback. `main` calls them in both orders so every callsite return
flows into another callsite's argument, exercising the cont-chain
seam where the bug lived.

The bug: codegen had a per-spec return-Descr fixpoint that ignored
`reachable_blocks` and didn't propagate through `Call`+continuation,
disagreeing with `module_types.effective_returns` (which the cont
side already uses). The `:err` arm's narrow `0` return got tag-boxed
into raw bits `1` and printed as such. fz-i82.2 deleted the
duplicate fixpoint; codegen now reads `effective_returns` directly.
