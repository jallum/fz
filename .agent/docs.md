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
| [../docs/dispatch-as-planner-output.md](../docs/dispatch-as-planner-output.md) | Planner-owned call-edge facts, `SpecPlan.call_edges`, `SpecKey` variants, or ReturnDemand capability selection. |
| [docs/externs.md](docs/externs.md) | `extern "C"` declarations, marshal classes, variadic calls, or extern codegen/interpreter behavior. |
| [docs/guides.md](docs/guides.md) | Writing or updating user-facing `guides/*.html`. |
| [docs/ir-planner-rename.md](docs/ir-planner-rename.md) | Renaming legacy phase/product/telemetry vocabulary to planner vocabulary. |
| [docs/ir-interp-runtime.md](docs/ir-interp-runtime.md) | IR interpreter runtime ownership, persistent drives, or REPL session execution. |
| [docs/lazy-continuation-materialization.md](docs/lazy-continuation-materialization.md) | Compiler-known native continuations, stack-backed continuation descriptors, closure materialization, or scheduler-boundary continuation roots. |
| [docs/modules.md](docs/modules.md) | Technical module interfaces, `.fzi` / `.fzo` artifacts, compiled units/images, link checks, or LTO boundary erasure. |
| [docs/module-separate-compilation.md](docs/module-separate-compilation.md) | Module identity, imports/interfaces, compiled units/images, runtime library modules, or LTO boundary erasure. |
| [../docs/protocols.md](../docs/protocols.md) | `defprotocol` / `defimpl`, protocol-domain types, implementation target identity, protocol dispatch, or no-replanning protocol/link rules. |
| [docs/physical-capabilities.md](docs/physical-capabilities.md) | Physical runtime-object capabilities, owned cons reuse, publication effects, or semantic/physical entry-param boundaries. |
| [docs/repl-session.md](docs/repl-session.md) | REPL world/bindings/runtime layering, chunk synthesis, docs/help, or macro/runtime boundaries. |
| [docs/reduction-yielding-plan.md](docs/reduction-yielding-plan.md) | Reduction-driven scheduler yielding, allocation-pressure budget expiration, continuation reserve policy, or removing GC-specific yield triggers. |
| [docs/reduction-yielding-review-gate.md](docs/reduction-yielding-review-gate.md) | Review gate and acceptance plans for reduction-yielding correctness gaps before building further on the reductions scheduler work. |
| [docs/scheduler-zero-arg-closures.md](docs/scheduler-zero-arg-closures.md) | Scheduler, receive, yield, spawn, timeout, or continuation re-entry. |
| [docs/any-value.md](docs/any-value.md) | `AnyValueRef`, `ValueRef`, raw scalar lanes, boxed scalars, pointer format, or GC-visible values. |
| [docs/telemetry.md](docs/telemetry.md) | Adding telemetry, testing compiler decisions, or measuring performance work. |
