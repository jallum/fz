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
- **`FactTable`** — one `FactSlot` per `FactKey`. A slot holds the contributions
  of every job that writes that key, the joined `value`, and a `revision`.
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

## Facts are owned, and they can shrink

A `FactSlot` aggregates `contributions: HashMap<Job, FactValue>`:

- **`FactValue::Presence(u64)`** — "this fact exists at this revision." Single
  owner in practice; the join is `max`.
- **`FactValue::Inputs(Vec<Ty>)`** — a real lattice value with many owners; the
  join is element-wise `refine_widen` (see `semantic-fixpoint`).

`replace_contributions` re-runs the join and bumps the slot `revision` **only
when the joined value actually changes** (exact `FactValue` equality, cheap
because `Ty` is an interned id — see `type-world`). The revision is a
change token, not a content hash; subscribers wake on `old_revision !=
new_revision`.

Each job rerun **replaces exactly the contributions it owns**. If a rerun stops
emitting a key, that contribution is dropped; if it was the last one, the slot
empties and the fact retracts. This is why redefinition needs no special path:
facts shrink as their owners stop deriving them.

## The drive loop

```text
while let Some(job) = agenda.pop():
    effects = run(job)              # may return Err -> fatal
    step    = complete(job, effects)
        replace reads/waits/outputs in deps
        join contributions, find changed facts
        enqueue each changed fact's subscribers + waiters, then follow_ups
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
