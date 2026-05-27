---
purpose: "receive matcher supports bitstring patterns without AST fallback"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 4
budget.codegen.instructions: 106
budget.specs.count: 3
budget.planner.worklist_pops: 6
budget.planner.walk_calls: 6
budget.planner.type_fn_calls: 3
budget.planner.matcher_specs: 0
budget.planner.vars: 23
budget.planner.blocks: 3
budget.planner.stmts: 12
budget.planner.dispatches: 1
---

# receive_bitstring_matcher

fz-puj.50 — bitstring receive clauses lower to first-class Matcher
bitstring tests. The matcher extracts fields while probing the mailbox,
then routes to the matching clause without using the receive AST pattern
walker.
