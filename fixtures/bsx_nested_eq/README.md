---
purpose: "fz-bsx.3 — nested structural == of a heap binary vs a utf8 string agrees on all paths (jit/aot match interp/repl)"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 5
budget.codegen.instructions: 136
budget.specs.count: 5
budget.planner.worklist_pops: 7
budget.planner.walk_calls: 7
budget.planner.type_fn_calls: 5
budget.planner.matcher_specs: 0
budget.planner.vars: 37
budget.planner.blocks: 7
budget.planner.stmts: 24
budget.planner.dispatches: 4
---

# bsx_nested_eq

Regression guard for fz-bsx: `Utf8.from_bytes(<<104,105>>) == {:ok, "hi"}`
compares a heap binary nested in a tuple against a utf8 string literal. The
brand is type-system metadata; runtime equality is bytewise, so every path
must agree (`true`). Before fz-bsx, native (jit/aot) folded this to `false`.
