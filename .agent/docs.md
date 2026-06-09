# Agent Docs Index

These docs are compact memory for current subsystem mental models. Use them
before touching an area where the shape of the system matters.

Read:

- [agent-docs](docs/agent-docs.md) — writing or revising `.agent/docs` guidance.
- [guides](docs/guides.md) — writing user-facing `guides/*.html`: voice, shape, callouts, and the compact contract each leaves the reader.
- [northstar](../northstar.html) — the current world model: lazy `runtime.fz` bootstrap, namespace savepoints, local interned `Types`/`Ty`, joined activation facts, exact semantic closure, artifact boundaries, and the worked quicksort / `Enum.reduce` examples.
- [fact engine](docs/fact-engine.md) — the domain-free fixpoint spine: jobs as rules, reads/waits/owned outputs, the deduped agenda, value-based fact slots with revisions, and the drive loop.
- [semantic fixpoint](docs/semantic-fixpoint.md) — the heart: activation inputs as joined facts, emergent discovery vs. the observe-only seal job, the key/value split, and the `Recursive`/`DispatchMask` keying facts.
- [pipeline](docs/pipeline.md) — source→artifact across the job families: demand from a root, lazy runtime code, the one-way artifact boundary, and retraction by fact ownership.
- [type world](docs/type-world.md) — the World-owned interned type kernel: `Ty` as an id, one threaded `Types`, and why cheap id-equality lets facts detect change without hashing.
- [quoted source](docs/quoted-source.md) — compiler2's Fz-shaped quoted-source substrate: `{heap, root}` keys, structural fingerprints, Elixir-shaped AST tuples, private metadata keys, and `ScopeSnapshot`-based `__MODULE__` / `__ENV__` projection.
- [set-theoretic types](docs/set-theoretic-types.md) — types as sets of values: axes/DNF, the two `Types` implementations behind one trait, schemes, brands/opaques, and the typing-vs-runtime predicate split.
- [type specialization](docs/type-specialization.md) — how compiler2 types one activation (value-flow over lowered steps, return as a union over reachable clauses) and why specialization stays finite.
- [specs](docs/specs.md) — the `@spec` contract engine: overload sets, scheme matching, application with overlap witnesses, higher-order callback evidence, and the upper-bound coverage check.
- [protocols](docs/protocols.md) — protocols as owned facts: callback surface + domain type, impl registration, and receiver-subtype dispatch (`resolve_protocol_call`) with lazy runtime-impl loading.
- [modules](docs/modules.md) — modules and namespaces: identity-on-reference, the Placeholder→Indexed→Scoped→Defined lifecycle, the namespace savepoint chain, two-pass scoping, and lazy runtime-library/prelude loading.
- [externs](docs/externs.md) — the `extern "C"` FFI door: the `ExternTy` wire alphabet, marshal classes + auto-resolution, borrow-only args, C-vs-fz return ABI, runtime variadic dispatchers + symbol resolution, and resource typing.
- [telemetry](docs/telemetry.md) — compile-time telemetry internals plus the emission contract, trace harness, and test-observability guidance.
- [runtime telemetry](docs/runtime-telemetry.md) — the runtime event contract (`process_exited`, `dbg`) and how tests observe a run without poking process internals.
- [parser syntax](docs/parser-syntax.md) — `src/parser` tokens→AST: Elixir surface syntax, keyword lists, no-parens calls, captures, and the desugar boundary.
- [dispatch matrix](docs/dispatch-matrix.md) — the shared `DispatchMatrix`/`DispatchGraph` model behind function heads, `case`, receive, guard helpers, and protocol dispatch.
- [pattern matching](docs/pattern-matching.md) — one decision model (`SourcePatternRows`→`PatternDispatchPlan`): test-first/project-second, payloads, and guards.
- [any value](docs/any-value.md) — the one-word runtime value model (`AnyValueRef`): tags, container storage, codegen value lanes, and GC.
- [charlists](docs/charlists.md) — fz has no charlist type; integer lists stay lists, text is a binary, and where rendering differs from Elixir.
- [pinned process register](docs/pinned-process-register.md) — how compiled code carries the current `Process*` and spends its reduction budget.
- [scheduler zero-arg closures](docs/scheduler-zero-arg-closures.md) — scheduler re-entry is one verb (run a closure): receive, timeout, spawn, and halt continuations.
- [reduction yielding](docs/reduction-yielding.md) — the per-process reduction budget that drives scheduler fairness and allocation-pressure GC.
- [fixtures](docs/fixtures.md) — the four-path fixture matrix: frontmatter, goldens, the Elixir oracle, and dump budgets.
