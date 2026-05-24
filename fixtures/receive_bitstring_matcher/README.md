---
purpose: "receive matcher supports bitstring patterns without AST fallback"
paths: [jit, interp, aot]
budget.codegen.functions: 5
budget.codegen.instructions: 883
budget.specs.count: 3
budget.typer.worklist_pops: 6
budget.typer.walk_calls: 6
budget.typer.type_fn_calls: 3
budget.typer.matcher_specs: 0
budget.typer.vars: 25
budget.typer.blocks: 5
budget.typer.stmts: 14
budget.typer.dispatches: 1
---

# receive_bitstring_matcher

fz-puj.50 — bitstring receive clauses lower to first-class Matcher
bitstring tests. The matcher extracts fields while probing the mailbox,
then routes to the matching clause without using the receive AST pattern
walker.
