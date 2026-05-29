# Agent Docs Index

These docs are compact memory for subsystem mental models. Use them before
touching an area where the shape of the system matters. They should explain the
major parts, the big idea that makes them fit together, and the policy choices
that keep future work aligned.

Read the one whose trigger matches what you are about to touch:

- [agent-docs](docs/agent-docs.md) — writing or revising `.agent/docs` guidance.
- [continuation-captures](docs/continuation-captures.md) — continuation ABI, closure captures, lambda captures, or capture pruning.
- [destination-passing](docs/destination-passing.md) — destination planning/passing IR, erased init-token facts, tuple/list/map construction lowering, or typed container field initialization.
- [dispatch-as-planner-output](../docs/dispatch-as-planner-output.md) — planner-owned call-edge facts, `SpecPlan.call_edges`, `SpecKey` variants, or ReturnDemand capability selection.
- [externs](docs/externs.md) — `extern "C"` declarations, marshal classes, variadic calls, or extern codegen/interpreter behavior.
- [guides](docs/guides.md) — writing or updating user-facing `guides/*.html`.
- [ir-planner-rename](docs/ir-planner-rename.md) — renaming legacy phase/product/telemetry vocabulary to planner vocabulary.
- [ir-interp-runtime](docs/ir-interp-runtime.md) — IR interpreter runtime ownership, persistent drives, or REPL session execution.
- [lazy-continuation-materialization](docs/lazy-continuation-materialization.md) — compiler-known native continuations, stack-backed continuation descriptors, closure materialization, or scheduler-boundary continuation roots.
- [modules](docs/modules.md) — technical module interfaces, `.fzi` / `.fzo` artifacts, compiled units/images, link checks, or LTO boundary erasure.
- [module-separate-compilation](docs/module-separate-compilation.md) — module identity, imports/interfaces, compiled units/images, runtime library modules, or LTO boundary erasure.
- [protocols](../docs/protocols.md) — `defprotocol` / `defimpl`, protocol-domain types, implementation target identity, protocol dispatch, or no-replanning protocol/link rules.
- [physical-capabilities](docs/physical-capabilities.md) — physical runtime-object capabilities, owned cons reuse, publication effects, or semantic/physical entry-param boundaries.
- [pinned-process-register](docs/pinned-process-register.md) — Cranelift pinned register, compiled `Process*` base pointer, process ABI offsets, or the `CURRENT_PROCESS` dual invariant.
- [repl-session](docs/repl-session.md) — REPL world/bindings/runtime layering, chunk synthesis, docs/help, or macro/runtime boundaries.
- [reduction-yielding](docs/reduction-yielding.md) — reduction-driven scheduler yielding, the per-process budget, allocation-pressure expiration, the continuation reserve, or boundary maintenance.
- [scheduler-zero-arg-closures](docs/scheduler-zero-arg-closures.md) — scheduler, receive, yield, spawn, timeout, or continuation re-entry.
- [state-transitions](docs/state-transitions.md) — calls, continuations, closure calls, join points, loopification, or `Enum.reduce` state-transition planning.
- [any-value](docs/any-value.md) — `AnyValueRef`, `ValueRef`, raw scalar lanes, boxed scalars, pointer format, or GC-visible values.
- [telemetry](docs/telemetry.md) — adding telemetry, testing compiler decisions, or measuring performance work.
