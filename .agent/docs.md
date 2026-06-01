# Agent Docs Index

These docs are compact memory for subsystem mental models. Use them before
touching an area where the shape of the system matters. They should explain the
major parts, the big idea that makes them fit together, and the policy choices
that keep future work aligned.

Read the one whose trigger matches what you are about to touch:

- [agent-docs](docs/agent-docs.md) — writing or revising `.agent/docs` guidance.
- [continuation-captures](docs/continuation-captures.md) — continuation ABI, closure captures, lambda captures, or capture pruning.
- [control-flow-lowering](docs/control-flow-lowering.md) — `if` / `case` / `cond` / `with` / `receive` lowering, arm continuation functions, joins, or tailness across branch boundaries.
- [destination-passing](docs/destination-passing.md) — destination planning/passing IR, erased init-token facts, tuple/list/map construction lowering, typed container field initialization, physical capabilities, or owned-cons reuse.
- [dispatch-as-planner-output](docs/dispatch-as-planner-output.md) — planner-owned call-edge facts, `SpecPlan.call_edges`, `SpecKey` variants, callable capabilities, or ReturnDemand capability selection.
- [single-authoritative-plan](docs/single-authoritative-plan.md) — the one `plan_module` codegen commits to, the `planner.planned` count, `plan_callable_capabilities` / `CapabilityPlan`, why destination lowering needs no re-plan, or why the capability pass keeps the return fixpoint.
- [externs](docs/externs.md) — `extern "C"` declarations, marshal classes, variadic calls, or extern codegen/interpreter behavior.
- [fixtures](docs/fixtures.md) — authoring or changing a fixture, the four-path matrix, pass/fail rules, the four expressive media, or the dump-budget mechanism.
- [guides](docs/guides.md) — writing or updating user-facing `guides/*.html`.
- [ir-interp-runtime](docs/ir-interp-runtime.md) — IR interpreter runtime ownership, persistent drives, or REPL session execution.
- [lazy-continuation-materialization](docs/lazy-continuation-materialization.md) — compiler-known native continuations, stack-backed continuation descriptors, closure materialization, or scheduler-boundary continuation roots.
- [modules](docs/modules.md) — module identity, interfaces, `.fzi` / `.fzo` artifacts, compiled units/images, import resolution, link checks, runtime-library modules, or LTO boundary erasure.
- [protocols](docs/protocols.md) — `defprotocol` / `defimpl`, protocol-domain types, implementation target identity, protocol dispatch, or no-replanning protocol/link rules.
- [pinned-process-register](docs/pinned-process-register.md) — Cranelift pinned register, compiled `Process*` base pointer, process ABI offsets, or the `CURRENT_PROCESS` dual invariant.
- [repl-session](docs/repl-session.md) — REPL world/bindings/runtime layering, chunk synthesis, docs/help, or macro/runtime boundaries.
- [reduction-yielding](docs/reduction-yielding.md) — reduction-driven scheduler yielding, the per-process budget, allocation-pressure expiration, the continuation reserve, or boundary maintenance.
- [scheduler-zero-arg-closures](docs/scheduler-zero-arg-closures.md) — scheduler, receive, yield, spawn, timeout, or continuation re-entry.
- [specs](docs/specs.md) — `@spec` parsing, validation, declared-call typing, interface/export specs, protocol callback specs, or multi-spec overload sets.
- [state-transitions](docs/state-transitions.md) — public `Enum.reduce` vs low-level `Enumerable.reduce` lowering, list reducer state machines, or known vs opaque reducers.
- [any-value](docs/any-value.md) — `AnyValueRef`, `ValueRef`, raw scalar lanes, boxed scalars, pointer format, or GC-visible values.
- [set-theoretic-types](docs/set-theoretic-types.md) — the type lattice (`Descr` axes, union/intersect/neg, emptiness/disjointness), brands & opaques as nominal refinements, brand erasure, and the two-model rule: runtime equality/matching is brand-blind (`is_value_disjoint`) while typing/dispatch/boundary is brand-aware (`is_disjoint`).
- [type-specialization](docs/type-specialization.md) — activation-based type inference over CPS IR: activations are keyed by `FnId` plus input facts, parameters do not default to `any`, proof rides beside visible `Ty`, call targets resolve to arrow sets, operators apply strict signatures, details emit through telemetry, and returns converge by monotone worklist plus finite-height widening.
- [parser-syntax](docs/parser-syntax.md) — surface syntax in `src/parser`: `fn` / `fnp` items, keyword lists, or `do`-block sugar.
- [range](docs/range.md) — Range's schema-backed Struct representation, runtime constructor, equality policy, and renderer behavior.
- [charlists](docs/charlists.md) — fz has no charlist type; how `dbg`/inspection renders integer lists, why it never emits `~c"..."`, and the consequence for Elixir-derived fixtures.
- [telemetry](docs/telemetry.md) — adding compile-time telemetry, testing compiler decisions, or measuring performance work.
- [runtime-telemetry](docs/runtime-telemetry.md) — runtime/scheduler telemetry events (`fz.runtime.process_exited`, `fz.runtime.dbg`), or observing a run in tests.
