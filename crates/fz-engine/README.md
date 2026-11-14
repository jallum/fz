# fz-engine

The fact engine: a generic fixpoint over jobs and facts. A client names its
job and fact types; the engine owns the agenda of jobs waiting to run, the
table of facts and who publishes them, the standing waits of jobs, and the
wake of a job when a fact it read moves. The engine has no World, no types and
no telemetry, and depends on nothing in the compiler. Its only dependency is
`foldhash`, for its own private hash tables (`src/fast_hash.rs`).

The compiler's `compiler2` module is the engine's client. The engine is
described in full in `.agent/docs/fact-engine.md`.

## Modules

- `scheduler`: `Scheduler<P, F>`, the agenda plus fact table plus dependency
  index. `complete_ordered` records one job run (`CompletionEffects`) and
  returns an `AppliedStep` (changed facts, fact movements, `Wake`s, standing
  waits). `settle_quiescent_ordered` settles the facts it is given once nothing can
  still move them.
  `DriveOutcome`, `FatalError`, `WorkStart` and `WorkStartTally` are the
  vocabulary a drive loop reports in. The engine originates two work-start
  reasons itself, `WorkStart::ChangedRevisionWake` (a wake) and
  `WorkStart::Unclassified` (an entry that names no reason); every other
  reason is the client's, carried as `WorkStart::Client`.
- `facts`: `FactTable`, `FactUse`, `FactChange`, `FactMovement`, `FactState`,
  `FactReadiness`, `FactReplace`, and the three client traits below.
- `deps`: `DependencyIndex` and `UnresolvedWait`: the reads and output claims
  of each publisher, the standing waits of each job, and the reverse indexes
  from a fact use to its readers and waiters.
- `agenda`: `Agenda<J>`, a job queue that holds each job at most once.
- `ordered_set`, `ordered_worklist`: `OrderedSet` (registration-order set) and
  `OrderedWorklist` (a min-heap under a caller-supplied comparison).

## What a client implements

- `Publisher` (`Clone + Eq + Hash + Debug`): the identity of one answer. Its
  associated `Run` is the job whose run produces the answer; `run()` maps an
  answer to its job and `of_run()` maps a job to the publisher of its own
  answer. A job that answers one question per run is its own publisher. Its
  associated `Reason` is the client's own set of work-start reasons
  (`ClientReason`): `slot()` is the reason's position in `Counts`, a fixed
  `[u64; N]` array the `WorkStartTally` keeps for the client's reasons, and
  `name()` is its telemetry spelling. `Scheduler::enqueue` takes anything
  convertible to `WorkStart<P::Reason>`, so a client passes its own reason
  directly.
- `ClaimShape` on the fact key: `is_cumulative()` declares whether the fact's
  content is a monotone join (cumulative) or overwrites (replacing).
- `SemanticOrd<Ctx>` on publishers, runs and fact keys: `semantic_cmp(&self,
  other, ctx)` is a total order owned by the client's context. The `*_ordered`
  entry points take the context and compare in this order where order is
  observable (queued fact changes, readers and waiters, unresolved waits), so
  no result depends on hash order. The engine provides
  the `FactUse<F>` impl, ordering by fact and then by readiness.
- `ExternalDependencyStates<F>` (optional): answers `external_state(&F)` for
  facts whose state the client owns outside the table.
  `NoExternalDependencyStates` declares there are none.

A job run reports itself as `CompletionEffects<P, F>`: a list of
`DerivationEffects` (each the publisher, the facts it read, the facts it
owns, and which of those changed) plus the set of `FactUse` waits that stopped
the run. `CompletionEffects::single` builds the shape of a job that answers one
question per run.
