# Pipeline: From Source To Artifact

The compiler turns submitted source plus a root request into a frozen, 
backend-ready program — and touches only what the root reaches. This doc traces 
that journey across the job families. The engine underneath is `fact-engine`; 
the semantic core is `semantic-fixpoint`.

## Identity first, work on demand

Referencing a module or an MFA allocates a stable id (`ModuleId`, `FunctionId`)
immediately; defining it later fills the slot behind that id. A function can be
*defined* without being *lowered*, *typed*, or *emitted*. Nothing past
definition happens unless a root reaches it, so an uncalled function stays a cold
definition fact and never grows an activation.

## The job families

All families share one agenda; "stratum" is a write boundary, not a pass.

```text
source    IndexCode, ScopeCode, DefineModule
            parse, build namespaces, define modules/functions  -> *Defined facts
body      LowerFunction
            one demanded function -> LoweredBody (+ generated lambda defs)
dispatch  ReifyGuardDispatch, PlanEntryDispatch
            guard-pure helpers and clause matching -> GuardDispatch/EntryDispatch
keying    DeriveRecursive, DeriveDispatchMask
            stable per-function facts used to canonicalize activation keys
semantic  SeedRoot, AnalyzeActivation, SealSemanticClosure
            the root-scoped type+demand fixpoint -> SemanticClosed
artifact  MaterializeRoot
            freeze the closed set -> MaterializedProgram
          DeriveAbiReady
            make ABI lanes, return delivery, and callable entries explicit -> AbiReadyProgram
          DeriveEmissionReady
            assign stable emission inventory -> EmissionReadyProgram
```

The artifact family is a one-way ladder:

```text
MaterializedProgram(root)
  -> AbiReadyProgram(root)
  -> EmissionReadyProgram(root)
```

Those rungs are derived mechanically from the closed artifact below them. They
do not reopen semantic discovery.

## A root's journey

```text
submit_root(main/0)
  SeedRoot(root)
    publishes RootEntry, and once main is defined + key facts exist:
      Activation(root, main, []) , Executable(...)
      follow-ups: LowerFunction(main), PlanEntryDispatch(main),
                  AnalyzeActivation(entry), SealSemanticClosure(root)
  AnalyzeActivation walks main, resolves callsites, contributes callee
    Activation/Executable facts -> the frontier grows itself (emergent)
  SealSemanticClosure observes the frontier; when it settles, writes
    SemanticClosed(root) and enqueues MaterializeRoot(root)
  MaterializeRoot freezes the closed set into MaterializedProgram(root)
  DeriveAbiReady(root) derives ABI lanes, return delivery, and callable-boundary facts
  DeriveEmissionReady(root) derives stable emission inventory for backend adapters
```

Each callee pulls its own `LowerFunction` / `PlanEntryDispatch` /
`DeriveRecursive` / `DeriveDispatchMask` as the analysis needs them, so the
strata interleave per function rather than running front-to-back.

## Runtime and built-ins are ordinary, lazy code

`Enum`, `Kernel`, and friends are not a special class and not a prelude phase.
The first reachable reference pulls the owning runtime module's source through
`ensure_runtime_module`, which submits it as ordinary code; the same
`IndexCode`/`ScopeCode`/`DefineModule` jobs index it. Unreached runtime
functions are never lowered. The prelude itself is just a namespace head saved
after bootstrap bindings — visibility, not a stage.

## The artifact boundary is one-way

`MaterializeRoot` reads `SemanticClosed(root)` and nothing else from the semantic
world. It clones the closed executable set, prunes each body to its reachable
clauses, and freezes each live callsite to its selected callee. It cannot ask a
type question or discover a new callee.

- If a constituent the closure named is missing, it does not improvise — it
  waits for a fresh closure (`SealSemanticClosure` re-runs).
- If a callsite the closure claimed is genuinely unresolvable, it is a fatal
  `incomplete-semantic-plan` diagnostic.

So semantics close, then artifacts consume; growth across that line is an error,
not a feature.

## Artifact ladder and fact taxonomy

`MaterializedProgram` is the first backend-owned snapshot. It is allowed to
carry only closed facts already proven by semantics:

- pruned lowered bodies for the closed executable frontier
- selected call edges
- return types and per-value types
- effect summaries
- frozen extern marshal classes

The next two rungs narrow the contract:

- `AbiReadyProgram` derives ABI lanes, explicit return delivery, and
  callable-boundary obligations from `MaterializedProgram` plus
  `ExecutableNeed`.
- `EmissionReadyProgram` assigns stable emission-local inventory over Compiler2
  ids so interpreter/JIT/AOT adapters can enumerate executable entries and
  callable entries without building their own registry.

Things that belong in Compiler2 artifact facts:

- selected call edges
- return delivery
- extern marshal classes
- effect summaries
- callable-boundary obligations
- stable emission inventory

Things that do not belong there:

- old `SpecPlan` as a backend artifact surface
- `SpecRegistry` or `SpecId` as semantic identity
- old `AbiFacts` sets such as `native_fns`, `cont_fns`, `cont_target_fns`, and
  `cont_extras_count`
- backend-specific callable wrapper signatures
- formatted telemetry payloads

This is why `fz-rh2.8.2` stays blocked behind the artifact-model arc: adapter
work should consume `EmissionReadyProgram`, not invent it while wiring backend
entry points.

Backend-facing work has one hard rule after `MaterializedProgram`: it may read
only the settled artifact ladder below it.

- `MaterializeRoot(root)` may consume only `SemanticClosed(root)`.
- `DeriveAbiReady(root)` may consume only `MaterializedProgram(root)` plus the
  world-owned type store.
- `DeriveEmissionReady(root)` may consume only `AbiReadyProgram(root)`.

If backend code needs to ask semantic, reachability, callee-selection, or
type-inference questions after that line, the artifact contract is incomplete
or the consumer is violating it. The fix is to publish the missing closed fact,
not to poke back into semantic state.

## Redefinition retracts by ownership

Redefinition is not a special path; it falls out of owned-output replacement.

```text
redefine main to drop the qsort call
  FunctionDefined(main) changes -> LowerFunction(main) -> LoweredBody(main)
  AnalyzeActivation(main) re-runs, stops contributing Activation(qsort,...)
    qsort had only main as caller -> slot empties -> Activation(qsort) retracts
    AnalyzeActivation(qsort) wakes, no input -> drops its outputs
      Activation(partition), Activation(append) lose their owners -> retract
  SealSemanticClosure re-runs over the smaller frontier, re-seals SemanticClosed
```

The blast radius is exactly the dependency chain, propagated by fact ownership.
A function that was defined but never reached is untouched: redefining it changes
its definition fact and wakes no semantic work for that root.
