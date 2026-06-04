---
purpose: "fz-bsx.4 — case-match of {:ok, \"hi\"} over a heap binary nested in a tuple matches on all paths"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 11
budget.codegen.instructions: 137
budget.specs.count: 11
budget.planner.worklist_pops: 11
budget.planner.walk_calls: 11
budget.planner.type_fn_calls: 11
budget.planner.matcher_specs: 0
budget.planner.vars: 35
budget.planner.blocks: 19
budget.planner.stmts: 23
budget.planner.dispatches: 11
---

# bsx_nested_match

Regression guard for fz-bsx: matching `{:ok, "hi"}` against
`Utf8.from_bytes(<<104,105>>)` must succeed (`:matched`) on every path. The
literal-binary pattern lowers to the same brand-blind equality fold as `==`;
before fz-bsx, native (jit/aot) pruned the arm and returned `:no_match`.
