---
purpose: "receive matcher supports bitstring patterns without AST fallback"
paths: [jit, interp, aot]
budget.codegen.min_functions: 5
budget.codegen.max_functions: 5
budget.codegen.min_instructions: 104
budget.codegen.max_instructions: 158
budget.specs.min_count: 10
budget.specs.max_count: 16
---

# receive_bitstring_matcher

fz-puj.50 — bitstring receive clauses lower to first-class Matcher
bitstring tests. The matcher extracts fields while probing the mailbox,
then routes to the matching clause without using the receive AST pattern
walker.
