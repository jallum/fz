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
          LowerBackendProgram
            attach settled call targets, callable-boundary obligations, and extern wire classes
            to structured function bodies -> BackendProgram
```

The artifact family is a one-way ladder:

```text
MaterializedProgram(root)
  -> AbiReadyProgram(root)
  -> EmissionReadyProgram(root)
  -> BackendProgram(root)
  -> NativeProgram(root)
```

Those rungs are derived mechanically from the closed artifact below them. They
do not reopen semantic discovery. `NativeProgram(root)` is intentionally a
separate lowering step above `BackendProgram(root)`, not an adapter-side query
back into semantic or planner state.

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
  MaterializeRoot freezes the closed set into MaterializedProgram(root),
    pruning unreachable clauses and turning semantically cold local-control
    entries into explicit halt stubs
  DeriveAbiReady(root) derives ABI lanes, return delivery, and callable-boundary facts
  DeriveEmissionReady(root) derives stable emission inventory
  LowerBackendProgram(root) derives the backend-consumable handoff
  LowerNativeProgram(root) derives the CPS/native handoff for compiler2-owned codegen
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

## Function-local control is an entry graph

`LoweredBlock { steps, result }` was enough for straight-line code plus a
special-cased `if`, but it was too weak for `case`, `with`, and `receive`.
Compiler2 now lowers one function body as:

- `LoweredClause`: head projections plus the `ControlEntryId` where the clause
  body starts
- `LoweredEntry`: one reusable local control node with `captures`, straight-line
  `steps`, and one `LoweredTail`
- `LoweredTail`: the only place control can branch, call, or return
- `ControlDestination`: either `Return` or `Deliver(next_entry)`

That makes local control explicit instead of positional.

- `ControlEntryOrigin::Clause` is a clause body entry.
- `ControlEntryOrigin::Branch` is a compiler-made join/arm entry.
- `ControlEntryOrigin::CallResume { value }` is where a non-tail call delivers
  its result before more work continues.
- `ControlEntryOrigin::LocalResume { value }` is where local control like
  `receive`, `if`, or `dispatch` delivers a value without creating a callable
  continuation boundary.

So a non-tail direct call is not "call, then keep walking the remaining steps."
It is:

```text
entry N:
  steps...
  tail = DirectCall { ..., dest: Deliver(resume_k) }

entry resume_k:
  origin = CallResume { value: v }
  captures = [...]
  steps...
  tail = ...
```

The backend and native jobs preserve this shape mechanically. They derive ABI
for resume entries, clause-entry helpers, and continuations from the same entry
graph instead of rebuilding hidden CPS structure from "tail position" guesses.
The backend interpreter preserves the same distinction: tail calls can park on
`receive`, and blocked tasks keep an explicit backend continuation stack so a
woken callee can still deliver into the caller's resume entry later.

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
  ids and carries forward the settled clause-entry dispatch each reachable
  executable needs at runtime.
- `BackendProgram` keeps the same closed inventory, but rewrites each
  structured body so direct calls point at executable inventory slots,
  callable-boundary arguments name the required callable-entry inventory, and
  extern callsites carry concrete wire classes. This is the interpreter-ready
  handoff.
- `NativeProgram` is the native-specific handoff above `BackendProgram`: a
  Compiler2-owned CPS/codegen-ready projection carrying direct executable
  bodies, clause helpers, continuations, callable-constructor metadata, and
  extern-marshal facts instead of rebuilt `ModulePlan`, `PlannedProgram`, or
  `AbiFacts`.

Things that belong in Compiler2 artifact facts:

- selected call edges
- return delivery
- extern marshal classes
- effect summaries
- callable-boundary obligations
- settled clause-entry dispatch
- stable emission inventory
- native-codegen handoff facts derived from `BackendProgram`

Things that do not belong there:

- old `SpecPlan` as a backend artifact surface
- `SpecRegistry` or `SpecId` as semantic identity
- old `AbiFacts` sets such as `native_fns`, `cont_fns`, `cont_target_fns`, and
  `cont_extras_count`
- backend-specific callable wrapper signatures
- formatted telemetry payloads

Interpreter work should consume `BackendProgram`, and native work should
consume `NativeProgram`, not invent old planner/codegen state while wiring
JIT or AOT entry points.

Backend-facing work has one hard rule after `MaterializedProgram`: it may read
only the settled artifact ladder below it.

- `MaterializeRoot(root)` may consume only `SemanticClosed(root)`.
- `DeriveAbiReady(root)` may consume only `MaterializedProgram(root)` plus the
  world-owned type store.
- `DeriveEmissionReady(root)` may consume only `AbiReadyProgram(root)`.
- `LowerBackendProgram(root)` may consume only `EmissionReadyProgram(root)` plus
  the world-owned type store.
- `LowerNativeProgram(root)` may consume only `BackendProgram(root)` plus the
  world-owned type store.

If backend code needs to ask semantic, reachability, callee-selection, or
type-inference questions after that line, the artifact contract is incomplete
or the consumer is violating it. The fix is to publish the missing closed fact,
not to poke back into semantic state.

## Native codegen contract

`NativeProgram(root)` is the last Compiler2-owned artifact before JIT/AOT
consumption. Native codegen is allowed to ask only backend-consumption
questions at that rung:

| Old shared-native input | Compiler2-native answer |
| --- | --- |
| prepared `Module` | `NativeProgram.module` |
| executable / helper inventory | `NativeProgram.entry` plus `NativeProgram.bodies[*].fn_id` and `origin` |
| `ModulePlan.effective_returns` and `fn_effects` | `NativeBody.return_ty`, `return_abi`, and `effects` |
| `SpecPlan.vars` type queries | `NativeBody.value_types` |
| `PlannedProgram.callable_entries` | `NativeProgram.callable_entries` |
| callable-constructor lookup through planner state | `NativeBody.callable_constructors` |
| extern decls plus wire classes | `NativeProgram.module.externs` plus `NativeBody.extern_marshals` |
| continuation / entry ABI classification | `NativeBody.entry_abi` and `NativeBodyOrigin::Continuation` |

Questions that are illegal after `NativeProgram(root)`:

- reading `ModulePlan`, `PlannedProgram`, `SpecPlan`, `SpecRegistry`, or
  `AbiFacts`
- asking reachability, callee-selection, or semantic-closure questions
- re-deriving callable-entry obligations, return lanes, or extern marshal
  classes from old-world planner state

During the in-house backend fork, compiler2 may temporarily carry copied
planner-shaped baggage (`SpecPlan`, `SpecRegistry`, synthetic `SpecKey`,
widened `return_tys`) as compiler2-local implementation detail. That baggage is
never part of the contract above. It is tolerated only inside the forked
compiler2 backend while parity is being established, and it remains a cleanup
target until the compiler2-native backend answers those questions directly from
`NativeProgram` / `NativeBody`.

Likewise, old semantic payloads still hanging off shared fz-IR structures
(`ExternDecl.ret_descr`, `ExternDecl.semantic_contract`, and similar) are not
authority for compiler2-native codegen after `NativeProgram(root)`. If the
compiler2 backend still reads them, that is backend debt to remove, not part of
the published handoff.

Current temporary exception: compiler2-native now projects compiler2-owned
types into an explicit `RuntimeTypeTestShim` before lowering runtime membership
questions. That shim is not a second semantic type system; it is a temporary
runtime-observable predicate layer used by both direct type-tests and cached
receive dispatch. Replacing it with a first-class runtime predicate is tracked
separately by `fz-rh2.14.6`.

Current conclusion from the code:

- no missing closed fact has been identified for the current compiler2-native
  codegen inputs
- the compiler2-native JIT fixture tests now consume `NativeProgram(root)`
  through the compiler2-owned backend fork directly
- `Compiler2::compile_root_jit`, `run_root_jit`, and `compile_root_aot` now
  consume that same compiler2-owned backend path directly, using the world's
  interned type store instead of a fresh legacy one
- `fz2` is now the side-by-side outer shell for those front doors: `fz2 run`,
  `fz2 interp`, and `fz2 build` submit source directly to Compiler2, seed
  `main/0`, and never reopen old planner or type-infer work
- the remaining work above this seam is cutover: switch or retire the old `fz`
  surface and remove the fallback plumbing once parity is proven

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
