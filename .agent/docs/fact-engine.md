# Fact Engine

The compiler works by running small rules over a shared table of facts until the
work runs out. There is no phase order. A rule reads some facts, writes some
facts, and the engine re-runs whoever cared when a fact changes. When the queue
empties, compilation is done.

The engine is domain-free. `Scheduler<J, F>` knows nothing about types, modules,
or fz — it moves jobs (`J`) and fact keys (`F`) around. The fz vocabulary lives
one layer up in `drive.rs` as the `Job` and `FactKey` enums; the type world and
telemetry live in `World`. Keeping the engine ignorant is what lets the same
loop drive parsing, lowering, type inference, and artifact emission.

## The pieces

- **`Agenda`** — a `VecDeque` plus a `HashSet`. `enqueue` is idempotent while a
  job is pending (a job queued ten times runs once); `pop` clears the set so a
  later fact change can queue it again. This is coalescing: duplicate *pending*
  work is suppressed, changed work never is.
- **`FactTable`** — one `FactSlot` per `FactKey`. A slot holds the set of
  `publishers` claiming the fact, the `dirty_publishers` queued to re-run, and
  a `revision` counter. Slots hold no values — typed values live in `World`
  stores; the fact gates their visibility. Derived states: **present** (any
  publisher), **retracted** (none — the slot drops), **settled** (present and
  no claimant dirty).
- **`DependencyIndex`** — five exact-keyed maps: `reads`↔`subscribers`,
  `waits`↔`waiters`, and `outputs`. Waking a fact's interested jobs is an O(1)
  lookup, not a scan.
- **`Scheduler`** — owns the agenda, facts, and deps, and exposes `complete`.
- **`World::drive`** — pops a job, runs it, applies its effects, repeats.

## Jobs are rules; effects are their contract

Every job returns `JobEffects`:

```text
reads     facts it used        -> "wake me when these change"   (subscriber)
waits     facts it needed but  -> "wake me when these appear"   (waiter; also
          could not read yet       counts as unresolved work)
outputs   (FactKey, FactValue) -> facts this job OWNS this run
```

A job that cannot proceed records `waits` and returns; it never names another
job to run. Restarting blocked work is the fact->producer map's job, not the
blocked job's: `World::demand_fact_producer` (`drive.rs`) maps a fact to its
single producing job, and every path that discovers a blocked wait —
`demand_blocked_wait_producers` at drain time, the standing activation and
root-entry frontier expansions, and the product pull driver's fact waits —
demands that producer through the map. A fact with more than one possible
producer (for example `ModuleInterface`, produced by either `DefineModule` or
`DefineModuleInterface` depending on whether the module has source state) maps
through the same runtime condition a demanding caller would otherwise inspect
itself, so the map still names exactly one producer for the fact's current
ground. A fact whose producer publishes it only as a co-output of a broader
job's conclusion (`ModuleIndexed`, `ProtocolDispatch`,
`ProtocolImplProviders`, `Executable`, `BackendProgram`, `NativeProgram`) has
no arm: its demand rides the mapped fact that gates the job that co-produces
it. Every fact with one sole-producing job gets an arm — including
`FunctionSource` (`Job::PublishFunctionSource`), `ExpandedFunctionSource`
(`Job::ExpandFunctionSource`), `EntryDispatch` (`Job::PlanEntryDispatch`), and
`MacroExecutable` (`Job::BuildMacroExecutable`), whose sole producers used to
be named directly by the blocked wait instead of through this map. A fact is
a co-output exception only when no single job is its sole producer, never
because a caller already knows which job to name.
Blocked work is not an error; exact waits are how ordering emerges without a
separate phase schedule.

No job names another job to run. A job that cannot proceed records a bare
wait (`JobEffects::wait_on_current(fact)`) and returns; the fact->producer map
is what restarts it. `JobEffects` has no `follow_up` field — nothing in the
engine or `World` enqueues a job by name from inside another job's
completion.

A job must record `reads` unconditionally for every fact its conclusion
consulted, including a fact that was absent at read time. A read gated on
`has_fact` (or any other presence check) drops the subscription exactly when
it is needed most: a conclusion reached because a fact was still empty is a
legitimate current answer, but without the read it can never be re-derived
once that fact's producer publishes later. This matters most for
growing indices with many independent publishers over the course of a
drive — a protocol's implementation-provider index gains an entry per
`defimpl` as more source is scoped, so a callsite that reads it while empty
still needs the standing subscription to re-wake when the next `defimpl`
lands. `demand_producer_if_needed` (`drive.rs`) relies on every producer
observing this: a job that has already run and concluded without claiming a
given fact is never re-demanded to produce it — it is skipped outright,
because a real subscription (not a stall-poke) is what re-runs it once that
fact appears.

## Waiting extends, concluding replaces

A completion's meaning bifurcates on its waits (`Scheduler::complete`):

- **Concluding** (waits empty) replaces: reads swap subscriptions, the output
  list replaces the job's claims, and retraction-by-omission is available and
  final. Facts shrink as their owners stop deriving them — redefinition needs
  no special path.
- **Waiting** (waits non-empty) extends: reads union into the standing
  subscriptions, listed outputs union into the standing claims, prior
  activation-input contributions stand, and every claim the job holds is
  marked dirty — a blocked publisher's facts are never settled. Pausing is
  not recanting; a transient wait cannot destroy still-valid published work.

## Claims declare their shape; ascents wake, ground shifts rebase

`FactKey::is_cumulative` declares each fact's content algebra: `ReturnType`
and `ActivationInputs` hold monotone joins maintained by their `World` stores
(content only grows between ground shifts); every other fact's content
overwrites. The scheduler classifies every content change:

- **Ascent** — first appearance, or growth of a cumulative fact from an
  unshifted publisher. Readers re-run and join. This is the within-epoch
  chaotic iteration: monotone transfers over finite chains converge to the
  unique least fixpoint on any fair schedule, so wake order is performance,
  never correctness.
- **Ground shift** — a retraction, a replacing fact's content change, or any
  change concluded by a rebased publisher. Each reader's claims go unsettled,
  the reader is flagged **rebased** and re-enqueued. A rebased job's next
  conclusion replaces its cumulative store values instead of joining (the
  only narrowing path) and its changes propagate as shifts in turn; equal
  recomputation propagates nothing, so the shift cone is exactly the set of
  jobs whose recomputed outputs actually differ — narrowing keeps today's
  minimal-rerun incrementality.

The revision is a change token, not a content hash: stores report `changed`
only on real content movement (equal joins are quiet), and subscribers wake on
`old_revision != new_revision`.

## The drive loop

```text
while let Some(job) = agenda.pop():
    effects = run(job)              # may return Err -> fatal
    step    = complete(job, effects)
        waiting?  extend reads/claims, dirty the job's claims
        else      replace reads/waits/claims (retraction final)
        classify each change: ascent -> wake; shift -> rebase + wake
        enqueue dependents
```

When the agenda drains, standing demands expand before the drive ends: every
submitted root demands its entry activation's analysis
(`World::demand_root_entry_analyses`), every discovered callee activation
demands its own analysis (`World::demand_activation_frontier_analyses`), and
every blocked waiter's fact names its single producer through the
fact->producer map (`World::demand_fact_producer` — the same expansion the
product fact-wait loops reach through `World::next_ready_job`). Both
activation-analysis expansions are first-run ignition only: each checks
`Scheduler::has_run` for its `AnalyzeActivation` job and skips a key that has
already run at least once, because the graph's own read/wait subscriptions
carry every later revision from there — a key whose first run blocked without
settling stays reachable through the blocked-waiter expansion instead, never
through repeated re-demand. A stall pass only re-demands a blocked fact after
some fact content changed, so byte-identical re-runs cannot loop. The loop
ends only when nothing can be demanded: `Resolved` (no waiters),
`Unresolved { waits }` (blocked facts with no mapped producer), or
`Fatal { job }`.

**Errors are not facts.** A job returning `FatalError` aborts the whole drive;
the diagnostic goes out through telemetry. Closure never masks an error, and
there is no diagnostics fact family to reconcile.

## Product pulls for artifacts

The interpreter artifact path is not a scheduler pass and it does not enqueue
follow-up jobs. `Compiler2::run_root_interp` asks the product driver for
`ProductKey::RootBackendProduct(root)`. Each product producer returns either a
`ProductValue` or an exact set of waits:

```text
ProductKey =
  RootBackendProduct(root)
  BackendExecutable(E)
  AbiExecutable(E)
  MaterializedExecutable(E)
  ExecutableEffects(E)
  RuntimeDemand(E)
  OutgoingInputEdges(E)
  IncomingInputSlot(slot)
  TransportShape(position)
  TransportComponent(position)
  CallableFacts(id)
  BoundaryFacts(id)

PullWait = Product(ProductKey) | Fact(FactUse<FactKey>)
```

The pull driver is the only code that expands a product wait into its producer.
A producer may say "I need `AbiExecutable(E)`" or "I need settled
`ReturnType(A)`"; it may not schedule unrelated work under another name.
Cyclic products settle their SCC inside one producer: `ExecutableEffects(E)`
and `RuntimeDemand(E)` each discover the dependency group containing `E` from
settled call-edge facts, run a bottom-start monotone ascent to the fixpoint,
and memoize the settled value for every member at once. A memoized product is
served from the session cache; settled demand retracts only on an epoch event
(re-materialization resolving a call edge outside the settlement's callee
inventory) or when a settlement's own publication grows the join of an
external input it consumed — then the producer re-collects with the displaced
external absorbed and re-settles the grown cone before memoizing. Fact
waits are satisfied at the Compiler2 front door by driving only the direct fact
producer needed for that exact fact, while deferring forbidden root artifact
jobs for the submitted root.

`PullSession` is request-local product state. It memoizes produced products and
records the symbolic inventory discovered by demanded products: materialized,
ABI, and backend executables; runtime demand; incoming input sources; transport
shapes/components; callable/boundary facts; and the final dense executable
index. The final dense `BackendProgram` packaging is the only root-wide assembly
step. It packages the symbolic backend executables already present in the
session; it does not scan the fact table to rediscover artifact membership.
Transport products are demand-derived session state: when an executable's
runtime demand or incoming input sources change, the session invalidates that
executable's cached transport shapes/components before rebuilding downstream
materialized, ABI, or backend products.
Runtime-demand products also record the other runtime-demand products they read.
When one settles to a changed value, only those recorded dependents are
invalidated; if a product is invalidated while in progress, the pull driver
rejects that stale result and returns an explicit product wait for the same key.

`BackendProgram(root)` is a co-output-only fact (no arm in
`World::demand_fact_producer`): its sole producer is this bounded product-pull
drive, `drive_root_backend_product`, never an agenda job. A job that needs a
root's `BackendProgram` as an ordinary prerequisite of its own conclusion --
`Job::BuildMacroExecutable` (`jobs/macro_runtime.rs`, building the executable
for a macro's hidden compile-time root) and `Job::LowerNativeProgram`
(`jobs/native.rs`, lowering a root's backend program to native) -- runs this
same bounded drive inline when the fact is absent and registers its result
through `complete_job`, exactly as `product_drive::drive_product_fact_wait`
already does for jobs it runs inside its own bounded fact-wait loop. This is
the second sanctioned non-wait work-start alongside `submit_root`'s `SeedRoot`
ignition: `submit_root` starts work because the root does not exist yet to be
waited on, while this starts work because the fact it needs has no producer a
wait could ever name -- both are bounded, self-contained drives invoked
directly rather than a job commanding another job to run.

### Whole-program struct-schema completeness

`World::struct_def_schemas()` snapshots the *entire* shared `StructDefMap` fact
store (every published `defstruct`, source-written or macro-emitted) at the
moment a root's `BackendProgram` is packaged (`jobs/backend.rs`,
`produce_root_backend_product`). That snapshot feeds `struct_schemas` on the
`BackendProgram`, which the interpreter and native codegen read for the
cofinite `is_named_struct`/`matches_runtime_struct` check ("is this runtime
value NOT one of the known named structs") — a check that needs completeness
over every struct name that could appear as a runtime value anywhere in the
program, not just ones the checking root's own reachable graph literally
constructs.

A `World` can hold more than one independently-driven `RootId` at once — every
`defmacro` mints its own hidden compile-time root (`World::macro_root`, driven
through `Job::BuildMacroExecutable`) alongside the program's one runtime root.
`struct_def_schemas()` is order-dependent in principle: it only contains what
has *settled so far*, and different roots settle their own backend products at
different times. Whole-program completeness nonetheless holds today, by
construction of two facts about the current architecture:

- **Per-root completeness is structural.** A root's `BackendProgram` cannot
  settle until every `BackendExecutable` its own reachable call graph needs has
  been packaged, and a `MakeStruct`/`StructField`/`AssertStruct` step cannot
  package until the struct it names has a settled `StructDefined` fact
  (`produce_root_backend_executable_product`'s waits). So whichever root reads
  `struct_def_schemas()` already has every struct *it itself* can construct or
  match against.
- **No struct value ever crosses between two independently-driven roots at
  runtime.** One `fz2 run`/`interp`/`build` invocation submits exactly one
  runtime root (`Compiler2::submit_root`, `RootKind::Runtime`); `fz2 test`
  spawns one fresh OS subprocess (and therefore one fresh `Compiler2`/`World`,
  with its own one runtime root) per discovered test via `run-test-root`; the
  fixture matrix likewise drives each fixture/path as its own child process.
  Spawned actor processes (`fz_spawn`) reuse the *same* `BackendProgram` their
  spawning root already produced — spawning mints a new runtime `Process`, not
  a new `RootId`. Macro roots run on a separate compile-time process
  (`QuotedSourceRoot::lend_process`) over AST-shaped values, never over the
  running program's own struct instances, and their product is never read by
  the main root's interpreter/codegen. So the one root whose reachable graph
  can construct a given struct is always the same root whose product is
  consulted when a value from that construction is later struct-checked.

Together these mean today's single-runtime-root-per-program execution model
makes the cofinite predicate sound by construction, even though
`struct_def_schemas()` itself has no barrier forcing it to wait for every
`defstruct` in the `World`. A future feature that lets one `World` drive
*multiple runtime roots* whose values can flow into each other at runtime (a
REPL, a multi-submission session, cross-program message passing) would break
this invariant and must add the coarser barrier this section describes instead
of relying on it implicitly.

## Tiny walkthrough

```text
LowerFunction(f) writes LoweredBody(f) @ rev 4
  FactTable: slot LoweredBody(f) value changed, rev -> 4
  deps.subscribers(LoweredBody(f)) = { AnalyzeActivation(a) }
  agenda.enqueue(AnalyzeActivation(a))      # it read LoweredBody(f) before
AnalyzeActivation(a) re-runs against the new body.
```

## Ownership boundaries

- **Engine** (`scheduler`/`agenda`/`facts`/`deps`): generic fixpoint over
  `(J, F)`. No types, no telemetry, no fz.
- **`World`**: owns the type interner and threads `&mut Types` into `complete`
  so the join can widen; owns the typed stores behind the facts.
- **Telemetry**: emitted at the `World` seam from the returned `AppliedStep`
  (`changed`, `enqueued`, `coalesced`, `blocked`), so observability is a
  consequence of the engine's output rather than a chore inside each rule.
