---
purpose: "spawn + send + receive — parent blocks on receive, prints the message"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 6
budget.codegen.instructions: 67
budget.specs.count: 4
budget.planner.worklist_pops: 7
budget.planner.walk_calls: 7
budget.planner.type_fn_calls: 4
budget.planner.matcher_specs: 0
budget.planner.vars: 15
budget.planner.blocks: 6
budget.planner.stmts: 9
budget.planner.dispatches: 1
---

# concurrency_ping_pong

spawn + send + receive — parent blocks on receive, prints the message

## Notes

fz-ul4.19 demonstration: parent + child processes with send/receive.

Parent (pid=1) spawns a child task. Child sends an integer message to
pid=1 (the parent's pid is hard-coded for this demo because v1 spawn
restricts to closures with zero captures — passing parent's pid into
the child via a closure capture is a follow-up to fz-ul4.19.2; see
.19.2's body for the v1 restriction).

Parent blocks on receive() until the child's message lands. Returns
the received value (42) as main's halt value.

Exercised end-to-end through the JIT pipeline (lex → parse → resolve
→ macros → ir_lower → ir_codegen → Runtime::run_until_idle) by the
unit test `fixture_ping_pong_via_jit_runtime` in src/runtime.rs.
