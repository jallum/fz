# Agent Docs Index

These docs are compact memory for current subsystem mental models. Use them
before touching an area where the shape of the system matters.

Read:

- [agent-docs](docs/agent-docs.md) — writing or revising `.agent/docs` guidance.
- [compiler2 northstar](../northstar.html) — the current Compiler2 world model: lazy `runtime.fz` bootstrap, namespace savepoints, local interned `Types`/`Ty`, joined activation facts, exact semantic closure, artifact boundaries, and the worked quicksort / `Enum.reduce` examples.
- [compiler2 fact engine](docs/fact-engine.md) — the domain-free fixpoint spine: jobs as rules, reads/waits/owned outputs, the deduped agenda, value-based fact slots with revisions, and the drive loop.
- [compiler2 semantic fixpoint](docs/semantic-fixpoint.md) — the heart: activation inputs as joined facts, emergent discovery vs. the observe-only seal job, the key/value split, and the `Recursive`/`DispatchMask` keying facts.
- [compiler2 pipeline](docs/pipeline.md) — source→artifact across the job families: demand from a root, lazy runtime code, the one-way artifact boundary, and retraction by fact ownership.
- [compiler2 type world](docs/type-world.md) — the World-owned interned type kernel: `Ty` as an id, one threaded `Types`, and why cheap id-equality lets facts detect change without hashing.
- [telemetry](docs/telemetry.md) — compile-time telemetry internals plus the Compiler2 emission contract, trace harness, and test-observability guidance.
