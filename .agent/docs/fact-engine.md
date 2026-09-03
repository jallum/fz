# Fact Engine

The compiler works by running small rules over a shared table of facts until the
work runs out. There is no phase order. A rule reads some facts, writes some
facts, and the engine re-runs whoever cared when a fact changes. When the queue
empties, compilation is done.

The engine is domain-free. `Scheduler<J, F>` knows nothing about types, modules,
or fz — it moves jobs (`J`) and fact keys (`F`) around. The fz vocabulary lives
one layer up in `drive.rs` as the `Job` and `FactKey` enums. Semantic state
lives in the lifetime-free `World`; `Compiler2` owns telemetry separately and
a short-lived `ExecutionContext` borrows both while driving. Keeping the engine
ignorant is what lets the same loop drive parsing, lowering, type inference,
and artifact emission.

## The pieces

- **`Agenda`** — a `VecDeque` plus a `HashSet`. `enqueue` is idempotent while a
  job is pending (a job queued ten times runs once); `pop` clears the set so a
  later fact change can queue it again. This is coalescing: duplicate *pending*
  work is suppressed, changed work never is.
- **`FactTable`** — one `FactSlot` per `FactKey`. A slot holds the set of
  `publishers` claiming the fact, the `dirty_publishers` queued to re-run, the
  `unfinal_publishers` whose own reads can still move, and a `revision`
  counter (1 on a replacing fact's appearance, 0 on a cumulative fact claimed
  at bottom). A publisher is a `Publisher<J>` — one job's one derivation — not a
  job. Slots hold no values — typed values live in `World` stores; the
  fact gates their visibility. Derived states: **present** (any publisher),
  **retracted** (none — the slot drops), **locally settled** (present and no
  claimant dirty), **quiet** (no claimant dirty and none unfinal — an absent
  fact is quiet), and **settled** (present and quiet). See *Content,
  cleanliness and finality* below.
- **`DependencyIndex`** — six exact-keyed maps: `reads`↔`subscribers` and
  `outputs` keyed by publisher, `waits`↔`waiters` keyed by job, and each job's
  `derivations` roster. Waking a fact's interested jobs is an O(1) lookup, not
  a scan.
- **`Scheduler`** — owns the agenda, facts, and deps, and exposes `complete`.
- **`ExecutionContext::drive`** — split-borrows semantic state and telemetry,
  then pops a job, runs it, applies its effects, and repeats.

## Jobs are rules; effects are their contract

Every job returns `JobEffects`:

```text
reads       facts it used        -> "wake me when these change"   (subscriber)
waits       facts it needed but  -> "wake me when these appear"   (waiter; also
            could not read yet       counts as unresolved work)
outputs     (FactKey, FactValue) -> facts this job OWNS this run
derivations further answers the same run reached independently, each with
            its own reads/outputs/changed
```

The flat `reads`/`outputs` are the job's WHOLE-BODY answer (`DerivationId::SOLE`);
`waits` are the job's, because a job blocks whole. `derivations` is empty for
every job today, which means one answer per job. See *The publisher is a
derivation* below.

A job that cannot proceed records `waits` and returns; it never names another
job to run. Restarting blocked work is the fact->producer map's job, not the
blocked job's: `World::demand_fact_producer` (`drive.rs`) maps a fact to its
single producing job, and every path that discovers a blocked wait —
`demand_blocked_wait_producers` at drain time, the standing activation
frontier expansion, and the product pull driver's fact waits —
demands that producer through the map. A fact with more than one possible
producer (for example `ModuleInterface`, produced by either `DefineModule` or
`DefineModuleInterface` depending on whether the module has source state) maps
through the same runtime condition a demanding caller would otherwise inspect
itself, so the map still names exactly one producer for the fact's current
ground. That condition may also name NO producer: `Activation`/
`ActivationInputs` map to `Job::SeedActivation` only while nothing else
supplies the activation's inputs (`World::seed_activation_producer`), because
a key a caller discovered is that caller's to publish and to withdraw. A fact
whose producer publishes it only as a co-output of a broader
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

A completion's meaning bifurcates per derivation, on whether the run reached it
(`Scheduler::complete`). A job with no waits reached every answer it reports:

- **Concluded** replaces: that derivation's reads swap subscriptions, its
  output list replaces its claims, and retraction-by-omission is available and
  final for every publisher whose silence is knowledge (see below). Facts
  shrink as their owners stop deriving them — redefinition needs no special
  path. A concluding job's UNREPORTED derivations are withdrawn the same way.
- **Unreached** extends: reads union into the standing subscriptions, listed
  outputs union into the standing claims, prior activation-input contributions
  stand, and every claim that derivation holds is marked dirty — an unreached
  answer's facts are never settled. Pausing is not recanting; a transient wait
  cannot destroy still-valid published work.

### One block per prerequisite set

A waiter re-runs only when EVERY fact it waits on is satisfied
(`Scheduler::wake_satisfied_waiters`), so waits registered together cost one
block and one wake however many they are. What a run asks for is therefore
free; WHEN it asks is not. A run that names one prerequisite, sleeps, and
reaches the next ask only once the first has landed pays a full re-evaluation
per rung and publishes nothing on the way — a ladder built inside one job
body, invisible to the scheduler, which sees only a job that blocked twice.
Every ask a run can already name belongs in the same pass.

`require_callee_prerequisites` (`jobs/semantic.rs`) is that shape: before a
call surface is refined, the callee's `FunctionContract` (when it declares
one) and the facts its activation key is built from (`Recursive`,
`InputDemand`) register in one pass, so a caller holding none of them blocks
once. Registering them a rung apart cost 65/30/33 of the 72/43/37 zero-change
`AnalyzeActivation` evaluations on the three measured fixtures; folding the
ask left 6/13/4 and moved no emitted byte (fz-kdt.86).

### Absence is bottom; rebasing is the narrowing path

The same reading applies one layer up, to the CLAIM. For a cumulative fact,
absence and bottom are the same answer: the store maintains a join, a join has a
bottom, and `World::activation_return` gates on revision presence and returns
`None` for both. So a first claim that carries no content — `analyze_activation`
claims `ReturnType` on every run, evidence or not — announces a publisher and
moves nothing. It is minted at revision **0**: present, at bottom, no content
movement (`facts::appearance_revision`), and `None` <-> `Some(0)` is not a
content change in either direction (`FactChange::content_changed`). `Current`
readers stay asleep; a `Current` wait is now satisfiable, and `Settled`
subscribers wake on the readiness edge. The first claim that carries real
evidence is an ordinary ascent, 0 -> 1.

A REPLACING fact has no bottom to be at, so this never applies to one: whatever
it says on arrival is content a reader can see and act on — `CallSiteSummary`
and `CallSiteTargets`' `Unresolved` IS a reader-visible answer, not the absence
of one — and it appears at revision 1 and wakes. The existence facts
(`Activation`, `Executable`) are the same: a whole cone is gated on their
presence.

Measured over `fz2 interp --log-telemetry` on `fz_f98_range_map_converges`,
`enum_predicate_search` and `00420_enum_take_drop_split`, joining each step's
`changed[old_revision=null]` against its `wakes[].cause` — of `ReturnType`'s
75/255/283 first claims, 46/152/135 carried no content, and those caused
43/137/139 `Current` wakes to re-read nothing. Removing them left the claims
exactly where they were and took 42/132/114 evaluations out of the compile,
almost all of them `AnalyzeActivation` runs that concluded unchanged (85 -> 43,
171 -> 37, 192 -> 72). No lifecycle, no shift count and no emitted byte moved
(fz-kdt.84). What that left standing was the callee-prerequisite ladder above:
those same three counts are 43/37/72 -> 13/4/6 since fz-kdt.86.

Retraction-by-omission is sound only where a publisher's silence about a key is
KNOWLEDGE. For `analyze_activation`'s callee `Activation` claims it is not: a
callsite whose target evidence is still climbing names no callee, and reading
that silence as a withdrawal retracts a fact that is still true. A NON-rebased
`AnalyzeActivation` conclusion therefore keeps every `Activation` claim it did
not re-emit (`World::preserved_analysis_claims`), exactly as its
`ActivationInputs` contributions ride
`ContributionMap::conclude_preserving_frontier`. Its `CallSiteSummary` and
`CallSiteTargets` claims are on the other side of the line: the walk publishes
an edge for EVERY callsite it reaches, unresolved and all
(`CallSiteResolution`, [`semantic-fixpoint`](semantic-fixpoint.md)), so silence
about one really is knowledge and nothing about those kinds is preserved. A
preserved claim is RE-LISTED, never re-published: its revision does not move, its stored
value is untouched, and no `Current` reader wakes (a readiness flip on a
re-listed key is representable and reaches `Settled` subscribers only). One
side effect is real: re-listed `Activation` keys pass
back through the completion's frontier harvest, so an unsettled callee is
re-noted on every preserving conclusion — bounded, and retired by the drain
pass's has-run guard.

Withdrawal is scoped, not lost. A REBASED conclusion re-derived every claim from
ground that actually shifted, so what it omits is genuinely refuted and ordinary
replacement retracts it — that is how redefining a body prunes the callees it no
longer reaches (`pipeline.md`, *Redefinition retracts by ownership*).
`Activation` is claimed by EVERY caller that reaches it, and each caller's claim
is withdrawn only by that caller's own rebase, so preserving one publisher's
standing claim never resurrects another's: the fact retracts exactly when the
last publisher with an unrefuted claim lets go.

## The publisher is a derivation

A job runs whole, but it does not necessarily reach ONE answer. The ledger's
publisher identity is therefore `(Job, DerivationId)`, not `Job`: `reads`,
`subscribers`, `outputs`, `dirty_publishers`, `unfinal_publishers` and
`unfinal_reads` are all keyed by it. A job that does not name derivations
publishes everything under `DerivationId::SOLE`, which is exactly the old
behavior.

Why the granularity was the lie: dirtiness and finality are statements about
what a claim was DERIVED FROM. With the job as publisher, one woken read
dirties every claim the body holds and unfinalises everything downstream of any
of them — so a fact whose own inputs are quiet reads as provisional because a
sibling answer's inputs moved. Measured on `00420_enum_take_drop_split`
(debug, this tree): `ActivationInputs` facts move 1.47x each (near
write-once) and almost never settle before the drain -- 30 of their 34
settlements arrive only after the first quiesce.

The two identities stay apart on purpose:

- the AGENDA, the `rebased` set and `waits`/`waiters` are keyed by the JOB,
  because a job blocks and runs whole, and a wait carries no derivation
  attribution to give it;
- a wake's cause names a derivation, so an ASCENT dirties only the derivation
  that read the moved fact. A GROUND SHIFT dirties every derivation of the
  woken job: rebasing selects replace-over-join for the job's next conclusion,
  and that flag is job-wide, so rebase vetoes all scoping;
- one cause wakes a job once, however many of its derivations read the fact.
  The `Wake` record's identity is still the job, because the job is what
  evaluates.

Completion bifurcates per derivation on whether the run REACHED it, which is
"waiting extends, concluding replaces" lifted one level down. A concluded
derivation replaces (its reads swap subscriptions, its unlisted keys retract,
its claims are clean); an unreached one extends (reads union, nothing retracts,
claims stay dirty). A job that returns no waits concluded every derivation it
reports, and the derivations it does NOT report are withdrawn whole — its
silence about an answer it used to give is knowledge, exactly as its silence
about a key is. A BLOCKED job may have reached some answers before the block:
those are clean, and the ones it never reached stay dirty. That is the main
traffic — most completions block.

`is_locally_settled`, `clear_unfinal_publishers` and the drain arbiter's
soundness argument hold VERBATIM at this granularity, because none of them was
ever about jobs: each is a statement about the CLAIMANTS of one key, and the
claimants of a key are the derivations whose answer it is. A dirty sibling
publishes other keys and is correctly not consulted. This is also why the
cheaper-looking alternative fails: per-output dirty bits sitting beside
per-JOB unfinality do not compose, because the two halves of `is_settled`
would then be scoped to different things.

## Claims declare their shape; ascents wake, ground shifts rebase

One job may own more than one fact when the two are the same derivation's
answers. `Job::DeriveCallGraphComponent` walks the `StaticCallees` edge facts
once and publishes both `CallGraphComponent(f)` -- the smallest `FunctionId`
mutually reachable with `f`, so "are these two functions mutually reachable"
is an equality of two fact reads rather than a traversal at the asking site --
and `Recursive(f)`, which that component decides. They stay two facts, not one
value: a component merging and a body's keying moving wake different readers.
`World::demand_fact_producer` maps both keys to the one job, exactly as
`Activation`/`ActivationInputs` both map to `SeedActivation` when that job is
their producer at all (see *One activation, one existence producer*).

## One activation, one existence producer

An activation's existence facts have exactly one producer, and which job that
is depends on how the key was reached. A root entry is `SeedRoot`'s: it
publishes `Activation`/`ActivationInputs` for its entry from the root's own
input. A callee reached over a call edge is its CALLER's: `analyze_activation`
publishes `Activation(callee)` and contributes the callee's input row, and
withdraws both only on a rebased conclusion. `Job::SeedActivation` owns the
third case and only the third case -- an activation the runtime-demand
frontier minted from a callable surface (`jobs::runtime_demand`), which no
analysis ever walked and no caller ever claimed. It reconstructs the inputs
from the key's own arrow, which is the truth only there.

`World::seed_activation_producer` (`drive.rs`) is where the map states this:
`SeedActivation` answers a demand for `Activation(k)`/`ActivationInputs(k)`
only while `ActivationInputs(k)` has no publisher. Once something else
supplies them, seeding could only overwrite another publisher's evidence with
a reconstruction -- and, because the reconstruction is unconditional, undo
that publisher's own withdrawal of the key, so no retraction of a
caller-discovered activation could ever stick.

The other half is `analyze_activation`'s own gate: an analysis whose
`Activation` fact is absent CONCLUDES rather than waits. Nothing claims the
key, so there is no producer for a wait to name; the run records the read
(the unconditional-read rule above), so a first or later claim wakes it, and
it re-lists its standing claims (`World::standing_claims`) so a conclusion
reached with no ground under it retracts nothing it never refuted.

`FactKey::is_cumulative` declares each fact's content algebra: `ReturnType`
and `ActivationInputs` hold monotone joins maintained by their `World` stores
(content only grows between ground shifts); every other fact's content
overwrites. The scheduler classifies every content change:

- **Ascent** — a first appearance carrying content, or growth of a cumulative
  fact from an unshifted publisher. Readers re-run and join. A cumulative
  fact's first claim at BOTTOM is not here at all: it is presence, not content
  (see *Absence is bottom*). This is the within-epoch
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

## Content, cleanliness and finality are three questions

They are asked of the same slot and answered separately.

- **Current content** — what the fact says right now, gated by `revision()`.
  A `Current` read takes the answer that stands.
- **Local cleanliness** — `is_locally_settled`: present, and no publisher is
  queued to re-run or paused on a wait. This is one hop. It says nothing about
  whether the publisher's own inputs have stopped moving.
- **Transitive finality** — `is_settled`: locally clean, AND no publisher is
  itself reading a fact that can still move. This is what `FactUse::Settled`
  projects, what the public stream's `settled` bit renders, and the only
  meaning of "settled" in the engine. `Settled(F)` means F's upstream cone is
  quiescent.

Finality is dependency STATE, maintained edge-triggered — never a pass, a
sweep, a group inventory, an epoch object, or a root scan. Two cached counts
carry it, and both are recomputed from their own source whenever that source
is replaced, so no delta can go stale:

    unfinal_reads[publisher]        how many of that derivation's recorded
                                    reads name a fact that is not quiet
    slot.unfinal_publishers         which publishers of the fact have a
                                    non-zero unfinal_reads

Both are keyed by the same publisher identity, which is what makes them
composable (see *The publisher is a derivation*). A fact flipping quiet adjusts
its readers' counts; a derivation whose count flips 0 <-> non-zero carries the
flip into every fact IT publishes — its siblings, which read other ground, are
untouched; a fact whose quiet state flips propagates on.
`Scheduler::unfinal_reads(job)` folds a job's derivations into the job-level
question a readiness-ordered pop would ask; the ledger itself always acts per
derivation. Every wave is sign-uniform — a fact that just
went unquiet can only make readers unquiet — so each node flips at most once
and the walk is exactly the affected cone.

Reading an ABSENT fact makes no reader unfinal. Nobody is deriving it, so
nothing about it can move on its own; a reader that concluded while it was
empty wakes on the fact's first CONTENT movement, which is a content change
like any other. Once someone claims the key, the ordinary rules take over: a
claim from a publisher that is still deriving makes the fact unquiet, and that
reader unfinalises through the same wave as any other reader.

A readiness-only change (a fact losing or regaining finality with the same
content) reaches `Settled` subscribers ONLY. Routing it
to `Current` subscribers as well would recompute formulas whose input content
never moved; `compiler2_scheduler_readiness_only_movement_evaluates_nobody`
holds that line.

### The drain arbiter

Counting cannot finalize a CYCLE. Take `A <-> B`, each fact published by a job
that reads the other: once both publishers are clean, A's count still holds B
and B's still holds A, and no local rule can lower either. The counts are
correct; the fixed point they describe is wrong the moment nothing is left to
run.

So at a drain — and only at a drain — the agenda decides. With no pending job,
the only publisher that could still move a fact is one paused on a wait, and a
paused publisher cannot run until something wakes it, at which point its claims
dirty and its readers unfinalize through the ordinary path. `Settled(F)` at a
drain is therefore exactly locally settled, which is what it meant everywhere
before finality became transitive. The transitive rule is what holds DURING the
ascent; the drain is where it is discharged.

`Scheduler::settle_quiescent(facts)` is that discharge, and it is
demand-driven: it answers the exact settled questions something is actually
asking — the blocked waiters' own settled waits (`World::settle_quiescent_waits`)
and a product pull's awaited fact (`product_drive::drive_product_fact_wait`).
Nothing else is arbitrated. One arbitrated
fact discharges a whole quiesced cycle, because clearing it makes it quiet and
the ordinary wave carries that through every publisher that was only waiting on
it.

Drain finality is optimistic in exactly the way settledness has always been
optimistic: a reader that acts on it may see the cone move again later, and it
re-wakes through the normal movement path. The flips are published as
`fz.compiler2.work_graph.quiesced` (`.agent/docs/telemetry.md`) so the settled
bit never changes without an event on the stream to name it.

## Wake order is not correctness, but it is reproducibility

"Any fair schedule reaches the same fixpoint" is a statement about fact
CONTENT. It is not a statement about the artifact. Two things downstream read
the schedule itself:

- the type interner mints ids as arena positions, so the order fresh types are
  first requested IS their numbering;
- a keep-first merge keeps whichever conclusion arrived first.

So a hash-random wake order publishes a different `BackendProgram` for the same
input — same structure, different `Ty` ids — while every fact is correct. Each
owner therefore makes unordered membership typed and explicit before the next
mutation boundary:

    job emits outputs (Vec, source order)
      -> dedupe_job_facts                  keeps order (OrderedSet, not HashSet)
      -> FactReplace::output_keys          keeps order
      -> DependencyIndex::outputs          keeps order
      -> mark_dirty                        iterates in that order
      -> pending_changes                   drained in that order
      -> DependencyIndex                   typed Publisher/Job order
      -> job order                         -> intern order -> Ty ids

`OrderedSet` still preserves source emission and membership, but insertion
order is not semantic identity. `DependencyIndex` orders subscriber, waiter,
reader, and unresolved-job waves with the World's typed Job/Publisher
relations. `ContributionMap` likewise orders every touched/next key wave before
joins can allocate. Losing owner order at any mutation boundary is sufficient
to move the first divergence downstream.

Two non-cures, both tried and rejected. Sorting needs a comparator that does not
depend on what is being minted, and Debug-text sorts are what fz-k22.21 had to
remove. A global after-the-fact renumbering pass of the interner is worse: it is
a barrier that needs the whole arena, it invalidates `Ty` as a stable handle for
every memo keyed by it, and it would leave the work order nondeterministic while
making only the ids look stable — hiding the defect instead of removing it.

Two tests hold this. `compiling_the_same_root_twice_runs_the_same_jobs_in_the_same_order`
is the causal one and names the first swapped pair;
`compiling_the_same_root_twice_publishes_byte_identical_backend_programs` is the
end state. Both compile twice in ONE process, which is what exposes the hazard:
`RandomState` is seeded per `HashMap` instance, so the second compile's maps
iterate differently from the first's.

Activation-bearing identities have one owner-supplied total order.
`SemanticOrd<Types>` compares real fields and delegates activation arrows to
`Types::cmp_activation_ty`. That operation reuses the type store's structural
walk in activation mode: callable arguments, return, then literal; list
emptiness and addressed variable paths remain explicit, and named literals use
immutable owner-registered callable labels. It therefore distinguishes lattice
forms that display intentionally merges, including possibly-empty and
non-empty lists, without allocating or parsing presentation text.
`Job`, `FactKey`, `FactUse`, callsites, executables, completion reports,
settled-wait drains, terminal unresolved inventories, product fact waits, and
activation dump/fixture inventories all delegate to that relation. `FactKey` has no
raw `Ord`: only the owning `World` can interpret its World-local type handles.
The generic scheduler and dependency index accept one semantic context whose
`SemanticOrd` implementations own fact, job, and publisher order; neither
accepts per-domain callbacks or falls back to type ids or hash iteration. Existing presentation
orders remain intact: diagnostics retain their variant-name order, readiness
is a tie-break after fact identity, and settled-wait draining uses that same
fact relation. Only activation-bearing payloads replace raw type ids with typed
structural comparison.

The type store memoizes `ActivationArrow` verdicts by a normalized `(low Ty,
high Ty)` pair; asking in the reverse direction reuses the inverse. Descriptors
and structural addresses are immutable after interning, and callable labels
must be registered before comparison and cannot be renamed, so the entry lives
for the owning `Types`/`World` lifetime with no invalidation path. Hit/miss
counters exist only in tests. ClauseOrder's private storage-canonical relation
remains distinct: it intentionally puts a closure literal before its surface to
group DNF clauses and must not determine activation order.

## The drive loop

```text
while let Some(job) = agenda.pop():
    effects = run(job)              # may return Err -> fatal
    step    = complete(job, effects)
        per derivation:
          unreached?  extend reads/claims, dirty that derivation's claims
          else        replace its reads/claims (retraction final)
        replace the job's waits; withdraw unreported derivations on conclusion
        classify each change: ascent -> wake; shift -> rebase + wake
        enqueue dependents (ascent scopes the dirt; shift dirties the job)
```

When the agenda drains, standing demands expand before the drive ends: every
published activation — root entry or caller-discovered callee — demands its
own analysis (`World::demand_activation_frontier_analyses`), and
every blocked waiter's fact names its single producer through the
fact->producer map (`World::demand_fact_producer` — the same expansion the
product fact-wait loops reach through `World::next_ready_job`). The activation
frontier expansion is first-run ignition only: it checks
`Scheduler::has_run` for its `AnalyzeActivation` job and skips a key that has
already run at least once, because the graph's own read/wait subscriptions
carry every later revision from there — a key whose first run blocked without
settling stays reachable through the blocked-waiter expansion instead, never
through repeated re-demand. A stall pass only re-demands a blocked fact after
some fact content changed, so byte-identical re-runs cannot loop. The loop
ends only when nothing can be demanded: `Resolved` (no waiters),
`Unresolved { waits }` (blocked facts with no mapped producer), or
`Fatal { job }`.

Standing waits come from a `HashMap`, but the dependency index does not guess
their identity. `DependencyIndex::unresolved` uses the same typed semantic
context as the other fact boundaries. Producer pokes and
the terminal `Unresolved` result therefore inherit one structural order across
opposite type-mint histories. This inventory is only materialized at the
existing stall and terminal boundaries.

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
  CallableResolution(E, value, surface)
  OutgoingEdgeFrontier(root)
  OutgoingInputEdges(E)
  IncomingInputRelations(root)
  IncomingInputSlot(slot)
  TransportShape(position)
  CallableConstruction(position)

PullWait = Product(ProductKey) | Fact(FactUse<FactKey>)
```

Before the pull stack expands an unordered wait set, product waits retain their
existing product-key order and fact waits use the World's semantic `FactUse`
key. Thus an activation-bearing fact cannot reverse product expansion merely
because its arrow received a different arena handle.

`ExecutableFacts(E)` is instead one direct fact. `DeriveExecutableFacts(E)`
publishes its World-owned immutable value after settled reads of
`ActivationAnalyzed(E.activation)`, `LoweredBody(E.function)`,
`EntryDispatch(E.function)`, and the exact `CallSiteSummary` facts named by the
analysis. Product producers read that settled fact through their ordinary fact
dependencies; no product memo entry or fact-to-product bridge exists.
`RuntimeDemand(E)` is read-only over those facts and its demand snapshot. Local
first-class calls request `CallableResolution(E, value, surface)`; a miss waits
and reruns, while success reads the producer's resolved edge.

The pull driver is the only code that expands a product wait into its producer.
A producer may say "I need `AbiExecutable(E)`" or "I need settled
`ReturnType(A)`"; it may not schedule unrelated work under another name.
The public causal stream records these as distinct operations: `requested`
means the stack asked for a key, `evaluated` means its producer body ran and
names the exact waits it returned, `settled` means a memo value was published,
`product.copublished` identifies a general publisher/peer settlement, and
`recursive_group.published` identifies every actual member of a successfully
settled recursive group. A repeated evaluation retains its prior exact waits
and the positions of the fact movement, settlement/cache hit, displacement, or
other exact event that triggered it. Each request has a checked, nonzero,
session-local id, and the producer-running request carries that same id on
`evaluated`. Exclusive driver ownership and the producer's context-only API
make overlapping pulls impossible; cache requests do not invent evaluations.
Recursive search inside a producer stays within that exact request boundary.
Causality is never inferred from an aggregate or merely adjacent log lines.
Cyclic products settle their SCC inside one producer: `ExecutableEffects(E)`
and `RuntimeDemand(E)` discover executable dependency groups from settled
call-edge facts; recursive `CallableConstruction(position)` products settle
their position groups from external anchors. `TransportShape(position)` has no
group: it cuts its own recursion from `CallGraphComponent` and `StaticCallees`
facts at recipe construction, so its evaluation is a function of settled facts
and of products that can settle without it. Component membership answers
mutual reachability, which is an equality; a grounded closure-call edge has no
static edge of its own. The group query records the prospective
`current -> dependency` read before borrowing the dependency map, so no graph
copy precedes the one Tarjan traversal that both detects a cycle and returns
the component containing the dependency. It follows the dependencies
of unsettled products only and visits each reachable product once. Hash order
may change visitation order, but not the search counts or component selected
from one graph. A settled product answers a read with the value it already
holds, so it waits on
nothing and no cycle of waits runs through it — and a settled product never
depends on an unsettled one, so nothing is missed by not stepping into it.
Graph traversal establishes component membership only. `ProductReadContext`
stages every peer value and dependency snapshot produced by one invocation;
`ProductDriver` adds the requested key, and `ProductMemo` typed-sorts and
commits that complete same-producer completion. Recursive components use the
same completion owner, which validates the group and publishes every member
atomically. This is an ordering envelope around one producer return, not a
batch across independent product pulls or fact settlements. Each memo entry
carries its immutable value, generation, exact product generations, and exact
fact-use states. `pull.recursive_group.searched` reports the traversal as query work; successful
`pull.recursive_group.published` events separately report exact actual members.
Both group-search and demand-cone measurements name their exact anchor
`ProductKey`; cone `members`/`rounds`/`derivations` measure fixpoint ascent, not
group discovery.
Every member of a settled group retains the union of the
group's external product and fact dependencies when every duplicate dependency
state agrees; a mixed-generation or mixed-fact-state snapshot publishes nothing
and retries from fresh reads. Internal back-edges disappear only after that
concordance check. Product or fact movement discards pending reader snapshots
and unregisters their edges before retry. Equal reproduction preserves its
generation. Settled demand retracts
when re-materialization resolves a call edge outside the settlement's callee
inventory, or when a settlement's own publication grows the join of an
external input it consumed — then the producer re-collects with the displaced
external absorbed and re-settles the grown cone before memoizing. Fact
waits are satisfied at the Compiler2 front door by driving only the direct fact
producer needed for that exact fact, while deferring forbidden root artifact
jobs for the submitted root.

`PullSession` owns the request-local product memo and scheduling relations used
to reproduce moved products. A `TransportShape(position)` answer remains in its
memo entry until an exact consumer reads it. `MaterializedExecutable` embeds the
positioned layout answers it consumed. A closure callee's carrier selects its
physical invocation: `ValueRef` uses the public wrapper, while `Absent` permits
one exact semantic target to refine directly. `AbiReadyExecutable` refines that
set and embeds each callable-construction answer with its position; and
`SymbolicBackendExecutable` carries both values unchanged. The root backend
packages a wrapper only from a positioned owner whose `construction` is
present. Direct-only owners retain their layout and direct callable facts with
no construction, so final packaging does not rejoin boundary publications to
recover first-class eligibility.

A value whose positioned layout settled to `Nothing` carries no lanes, so
nothing downstream can read it. Backend lowering applies that proof once, in the
shared symbolic lowering: every fresh construction step
(`Tuple`/`List`/`Map`/`MapUpdate`/`Struct`/`Bitstring`/`FunctionRef`/`Lambda`)
goes through `construction_step_or_omitted` and becomes `BackendStep::Omitted`
when its own value is proven absent — a closure the plan proves is never invoked
is never built, on any path. Runtime consumers therefore read an artifact that
already carries no dead construction. The proof is derived once, in lowering;
the runtimes honor it rather than re-derive it for constructions — an `Omitted`
step binds an absent value in both runtimes, and call-argument encoding elides
any position whose layout carries no reprs, so an absent operand is skipped by
the same fact that omitted its construction. The same proof holds at the other
end of a body: a return contract whose layout publishes no lanes has nothing to
encode, so a value tail returning through it reads no value at all
(`return_lane_vars` in `jobs/native.rs`, the `BackendTail::Value` arm in
`ir_interp/backend.rs`).

The root backend producer traverses its exact reachable backend-product
values, then densifies
their embedded layouts and callable owners into one root product answer. The
answer retains that `MaterializedTransportPlan` beside the closed
`BackendProgram`; runtime consumers project only the program.
There is no parallel session map of transport positions, shapes, layouts,
callable boundaries, or transport-shape groups, and final packaging does not scan the
fact table or memo to rediscover them.
Outgoing publication is normalized once into an immutable, typed-sorted
executable slice. `IncomingInputRelations(root)` and `OutgoingInputEdges`
share a private immutable ordered slot/source value, and each
`IncomingInputSlot(slot)` projects an immutable typed-sorted source slice.
Hash maps and sets are ephemeral construction tools only; no consumer can
observe their iteration order.
Runtime-demand products also record the other runtime-demand products they read.
When one settles to a changed value, only those recorded dependents are
invalidated; if a product is invalidated while in progress, the pull driver
rejects that stale result and returns an explicit product wait for the same key.

Today every backend request constructs a fresh `PullSession`; scheduler facts
live in `Compiler2`, but product generations and dependency edges do not cross
that request boundary. `backend_request.started` / `finished` bracket the
external request independently of nested sessions. One lifecycle gate emits
both boundaries with the same typed payload shape; finish records either final
population or failure, including when only one boundary has a direct
subscriber. Request-scoped causal replay therefore reports an unchanged or
unreachable-edit request's first-generation products as cross-request
recomputation rather than retained cache hits. This is the baseline the
long-lived-session work changes; the report survives as its work-count
regression signal. Each pull session also has a balanced
`pull.session.started` / `finished` lifecycle carrying one exact id. Replay keys
evaluation and movement history by that id, so a nested macro session neither
inherits nor clears its outer session's history; the same model already permits
one retained session to span multiple backend requests.

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

Freshness stays on those owners: the fact slot revision records published
`BackendProgram(root)` movement, and product generations reject stale pull
results. Neither `BackendProgram` nor its `NativeProgram` projection embeds a
second revision field; their equality compares artifact content directly.
`MacroExecutable.backend_revision` is deliberately different: it snapshots the
live backend fact revision used to build a compile-time executable.

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
- **`World`**: lifetime-free semantic state that owns the type interner and
  threads `&mut Types` into `complete` so the join can widen; owns the typed
  stores behind the facts. Semantic operations neither accept nor dispatch
  telemetry. A typed context may sequence observation after one of these
  operations, but mutation authority remains in `World`.
- **`ExecutionContext`**: a short-lived split borrow of `&mut World` and
  `&T` for the compiler's concrete `T: Telemetry`. It completes the scheduler
  mutation first, then emits activation-input and `AppliedStep` observations
  from raw borrows of the settled `World`. Thus handlers see the published
  fact and revision, and a `NullTelemetry` instantiation remains
  monomorphizable to no observation work. Its other observer wrappers follow
  the same rule: call one observer-free `World` semantic core, then emit from
  the returned decision and immutable `World` getters; the context never owns
  store mutation or invariants.

`AppliedStep<J, F>` is `Scheduler::complete_ordered`'s report of one completion's
effect on the graph: `changed` (the `FactChange`s that resulted), `movements`
(the full post-wave state of every fact this completion or its cascade
touched), `wakes`, and `blocked` (the waits, if any, this completion left
standing). Published keys remain authoritative in the scheduler's per-job
claim ledger; completion does not rebuild them for observation.
`wakes: Vec<Wake<J, F>>` is
every wake this completion caused, in wake order; each `Wake` attributes one
`job` to the `cause: FactUse<F>` that moved it, carries `disposition`
(`Enqueued` — the job's real work start — or `Coalesced` — the job was
already pending) and `shift` (the same ground-shift-vs-ascent classification
`complete` computed for `cause`). A job can carry more than one `Wake` in one
`AppliedStep`: `enqueue_step` records one per cause, so a job coalesced by
two distinct causes in the same `complete` call gets two `Wake`s, not one
deduped entry — coalescing a job's *evaluation* must not coalesce away *why*
it woke. This replaced the earlier `enqueued: Vec<J>` /
`coalesced: Vec<J>` fields, which reported only the deduped job lists with no
cause attribution.
