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

The generic scheduler still runs legacy/source/semantic jobs. A job returns
`JobEffects`:

```text
reads     facts it used        -> "wake me when these change"   (subscriber)
waits     facts it needed but  -> "wake me when these appear"   (waiter; also
          could not read yet       counts as unresolved work)
outputs   (FactKey, FactValue) -> facts this job OWNS this run
follow_up legacy jobs to enqueue now
```

A job that cannot proceed records `waits` and returns. Legacy jobs may also
name `follow_up` jobs, but new artifact producers must not use that mechanism:
artifact work is demanded by `ProductKey` through the pull driver below.
A follow-up is a demand that a producer run, not a changed-revision wake: one
naming a job whose conclusion still stands — it concluded and no fact it reads
moved since (`Scheduler::conclusion_stands`) — coalesces with that standing
conclusion instead of re-running it byte-identically. First runs, waiting
jobs, and rebased jobs still enqueue.
Blocked work is not an error; exact waits are how ordering emerges without a
separate phase schedule.

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
        enqueue dependents, then legacy follow_ups
            (a follow_up whose target's conclusion stands coalesces, no re-run)
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
