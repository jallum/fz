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

A job returns `JobEffects`:

```text
reads     facts it used        -> "wake me when these change"   (subscriber)
waits     facts it needed but  -> "wake me when these appear"   (waiter; also
          could not read yet       counts as unresolved work)
outputs   (FactKey, FactValue) -> facts this job OWNS this run
follow_up jobs to enqueue now
```

A job that cannot proceed records `waits` and the `follow_up` jobs that will
produce them, then returns. It is not an error to be blocked; it is how
ordering emerges without a schedule.

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
        enqueue dependents, then follow_ups
```

The loop ends as `Resolved` (agenda empty, no waiters), `Unresolved { waits }`
(stuck waiters remain — a missing definition or demand), or `Fatal { job }`.

**Errors are not facts.** A job returning `FatalError` aborts the whole drive;
the diagnostic goes out through telemetry. Closure never masks an error, and
there is no diagnostics fact family to reconcile.

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
