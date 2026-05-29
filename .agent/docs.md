# Agent Docs Index

These docs are compact memory for subsystem mental models. Use them before
touching an area where the shape of the system matters. They should explain the
major parts, the big idea that makes them fit together, and the policy choices
that keep future work aligned.

Read the one whose trigger matches what you are about to touch:

- [docs/agent-docs.md](docs/agent-docs.md) — writing or revising `.agent/docs` guidance.
- [docs/continuation-captures.md](docs/continuation-captures.md) — continuation ABI, closure captures, lambda captures, or capture pruning.
- [docs/destination-passing.md](docs/destination-passing.md) — destination planning/passing IR, erased init-token facts, tuple/list/map construction lowering, or typed container field initialization.
- [../docs/dispatch-as-planner-output.md](../docs/dispatch-as-planner-output.md) — planner-owned call-edge facts, `SpecPlan.call_edges`, `SpecKey` variants, or ReturnDemand capability selection.
- [docs/externs.md](docs/externs.md) — `extern "C"` declarations, marshal classes, variadic calls, or extern codegen/interpreter behavior.
- [docs/guides.md](docs/guides.md) — writing or updating user-facing `guides/*.html`.
- [docs/ir-planner-rename.md](docs/ir-planner-rename.md) — renaming legacy phase/product/telemetry vocabulary to planner vocabulary.
- [docs/ir-interp-runtime.md](docs/ir-interp-runtime.md) — IR interpreter runtime ownership, persistent drives, or REPL session execution.
- [docs/lazy-continuation-materialization.md](docs/lazy-continuation-materialization.md) — compiler-known native continuations, stack-backed continuation descriptors, closure materialization, or scheduler-boundary continuation roots.
- [docs/modules.md](docs/modules.md) — technical module interfaces, `.fzi` / `.fzo` artifacts, compiled units/images, link checks, or LTO boundary erasure.
- [docs/module-separate-compilation.md](docs/module-separate-compilation.md) — module identity, imports/interfaces, compiled units/images, runtime library modules, or LTO boundary erasure.
- [../docs/protocols.md](../docs/protocols.md) — `defprotocol` / `defimpl`, protocol-domain types, implementation target identity, protocol dispatch, or no-replanning protocol/link rules.
- [docs/physical-capabilities.md](docs/physical-capabilities.md) — physical runtime-object capabilities, owned cons reuse, publication effects, or semantic/physical entry-param boundaries.
- [docs/pinned-process-register.md](docs/pinned-process-register.md) — Cranelift pinned register, compiled `Process*` base pointer, process ABI offsets, or the `CURRENT_PROCESS` dual invariant.
- [docs/repl-session.md](docs/repl-session.md) — REPL world/bindings/runtime layering, chunk synthesis, docs/help, or macro/runtime boundaries.
- [docs/reduction-yielding.md](docs/reduction-yielding.md) — reduction-driven scheduler yielding, the per-process budget, allocation-pressure expiration, the continuation reserve, or boundary maintenance.
- [docs/scheduler-zero-arg-closures.md](docs/scheduler-zero-arg-closures.md) — scheduler, receive, yield, spawn, timeout, or continuation re-entry.
- [docs/state-transitions.md](docs/state-transitions.md) — calls, continuations, closure calls, join points, loopification, or `Enum.reduce` state-transition planning.
- [docs/any-value.md](docs/any-value.md) — `AnyValueRef`, `ValueRef`, raw scalar lanes, boxed scalars, pointer format, or GC-visible values.
- [docs/telemetry.md](docs/telemetry.md) — adding telemetry, testing compiler decisions, or measuring performance work.
