---
purpose: "receive matcher supports bitstring patterns without AST fallback"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 11
budget.codegen.instructions: 229
budget.specs.count: 10
budget.planner.worklist_pops: 10
budget.planner.walk_calls: 10
budget.planner.type_fn_calls: 10
budget.planner.matcher_specs: 0
budget.planner.vars: 28
budget.planner.blocks: 10
budget.planner.stmts: 11
budget.planner.dispatches: 10
---

# receive_bitstring_matcher

fz-puj.50 — bitstring receive clauses lower to first-class Matcher
bitstring tests. The matcher extracts fields while probing the mailbox,
then routes to the matching clause without using the receive AST pattern
walker.
