# Agent Docs Index

These docs are compact memory for subsystem mental models. Use them before
touching an area where the shape of the system matters. They should explain the
major parts, the big idea that makes them fit together, and the policy choices
that keep future work aligned.

| File | Trigger |
| --- | --- |
| [docs/agent-docs.md](docs/agent-docs.md) | Writing or revising `.agent/docs` guidance. |
| [docs/continuation-captures.md](docs/continuation-captures.md) | Continuation ABI, closure captures, lambda captures, or capture pruning. |
| [docs/destination-passing.md](docs/destination-passing.md) | Destination planning/passing IR, erased init-token facts, tuple/list/map construction lowering, or typed container field initialization. |
| [../docs/dispatch-as-planner-output.md](../docs/dispatch-as-planner-output.md) | Planner-owned dispatch facts, `SpecPlan.dispatches`, `SpecKey` variants, or ReturnDemand capability selection. |
| [docs/guides.md](docs/guides.md) | Writing or updating user-facing `guides/*.html`. |
| [docs/ir-planner-rename.md](docs/ir-planner-rename.md) | Renaming legacy phase/product/telemetry vocabulary to planner vocabulary. |
| [docs/ir-interp-runtime.md](docs/ir-interp-runtime.md) | IR interpreter runtime ownership, persistent drives, or REPL session execution. |
| [docs/lazy-continuation-materialization.md](docs/lazy-continuation-materialization.md) | Compiler-known native continuations, stack-backed continuation descriptors, closure materialization, or scheduler-boundary continuation roots. |
| [docs/repl-session.md](docs/repl-session.md) | REPL world/bindings/runtime layering, chunk synthesis, docs/help, or macro/runtime boundaries. |
| [docs/scheduler-zero-arg-closures.md](docs/scheduler-zero-arg-closures.md) | Scheduler, receive, yield, spawn, timeout, or continuation re-entry. |
| [docs/any-value.md](docs/any-value.md) | `AnyValueRef`, `ValueRef`, raw scalar lanes, boxed scalars, pointer format, or GC-visible values. |
| [docs/telemetry.md](docs/telemetry.md) | Adding telemetry, testing compiler decisions, or measuring performance work. |
