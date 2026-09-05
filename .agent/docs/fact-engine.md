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
`ProtocolImplProviders`, `Executable`) has
no arm: its demand rides the mapped fact that gates the job that co-produces
it. Every fact with one sole-producing job gets an arm — including
`FunctionSource` (`Job::PublishFunctionSource`), `ExpandedFunctionSource`
(`Job::ExpandFunctionSource`), and `EntryDispatch` (`Job::PlanEntryDispatch`). A fact is
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
(`Activation`, `Executable`) are the same: their readers are gated on presence.

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

`is_locally_settled` and drain arbitration inspect the exact derivations
claiming the requested key, not every answer of their jobs. Certifying one
clean derivation certifies its own co-outputs because they share its reads;
a dirty sibling derivation and another publisher's claims remain untouched.
Per-output dirty bits sitting beside per-JOB unfinality do not compose,
because the two halves of `is_settled`
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
sweep, a group inventory, an epoch object, or a root scan. The reader state and
claim state share one publisher identity:

    read_finality[publisher]        Pending(count) or Quiescent(count), tracking
                                    that derivation's actual unquiet read uses
    slot.unfinal_publishers         publishers whose reader state is Pending

An absent reader entry means zero unquiet reads. Replacing a derivation's reads
recounts them and removes any old quiescence certificate. Exact quiet edges
decrement the count; an unquiet edge increments it and revokes certification.
A change in effective finality reaches every output of that derivation — not
sibling derivations that read other ground. A fact whose quiet state flips
propagates on.

`Scheduler::unfinal_reads(job)` sums pending counts across a job's derivations
for readiness-ordered selection; quiescent-certified counts contribute zero.
The ledger itself always acts per derivation. Every wave is sign-uniform — a
fact that just went unquiet can only make readers unquiet — so each node flips
at most once and the walk is exactly the affected cone.

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

`Scheduler::settle_quiescent_ordered_with_external(facts, external, ctx)` is
that discharge, and it is
demand-driven: it answers the exact settled questions something is actually
asking — the blocked waiters' own settled waits (`World::settle_quiescent_waits`)
and one product evaluation's exact prerequisite set
(`product_drive::drive_product_fact_waits_with_sessions`). A product producer
names every prerequisite it can identify in the same evaluation, and the pull
driver presents that set to the arbiter atomically; serially arbitrating the
members would turn one semantic barrier into multiple public readiness steps.
Arbitration starts only from those requested facts. The selected fact must be
locally clean and have no unsettled external-product ground. For each of its
exact publishers, the scheduler records quiescent certification while retaining
the actual unquiet-read count, and clears that publisher's unfinal claims through
its existing output frontier.
Other publishers of a shared output still control their own claims. Ordinary
quiet propagation carries the resulting readiness edges to readers.

A derivation's co-outputs are one conclusion over the same reads, not separate
arbitration requests. Certifying the publisher's finality state together with
its claims ensures that a later
quiet-to-unquiet input edge revokes certification and unfinalizes all of them
again. The real count still includes previously licensed unquiet reads, so
their later quiet edges cannot cancel a different outstanding dependency.
No value or revision changes during this certification.

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
`ProductKey::RootBackendProduct(root)`. Each product producer returns a
`ProductValue`, an exact set of waits, or an explicit `Failed(ProductFailure)`
outcome that the memo never installs:

```text
ProductKey =
  RootBackendProduct(root)
  RootBackendContent(root)
  NativeProgram(root)
  BackendExecutable(E)
  AbiExecutable(E)
  MaterializedExecutable(E)
  ExecutableEffects(E)
  TransportShape(position)
  CallableConstruction(position)

PullWait = Product(ProductKey) | Fact(FactUse<FactKey>)
```

Before the pull stack expands an unordered wait set, product waits retain their
existing product-key order and fact waits use the World's semantic `FactUse`
key. Thus an activation-bearing fact cannot reverse product expansion merely
because its arrow received a different arena handle.

`ExecutableFacts(E)` and `RuntimeDemand(E)` are direct facts.
`DeriveExecutableFacts(E)`
publishes its World-owned immutable value after settled reads of
`ActivationAnalyzed(E.activation)`, `LoweredBody(E.function)`,
`EntryDispatch(E.function)`, and the exact `CallSiteSummary` facts named by the
analysis. `DeriveRuntimeDemand(E)` waits for that fact's first settled value,
then subscribes to its Current content, its exact caller-owned input cell, and
the `RuntimeDemandInputs(target)` sub-facts named by direct or first-class
callable edges. `CallableConstructionTarget(owner, value, surface)` supplies an
exact first-class target. Newly exposed local callables extend that finite
keyed read set until it stops growing; there is no function or executable scan.
Absence is bottom. An owned formula publishes provisional demand and
caller-local return contributions, then withholds only peer-dependent
capture/input contributions while an exact non-self target is absent. Product
producers read settled full `RuntimeDemand(E)` values through ordinary fact
dependencies; neither demand fact has a product memo entry or bridge.

Executable-scoped producers ask for `ExecutableFacts(E)`, `RuntimeDemand(E)`,
and every position-owned semantic fact nameable from the key in the same
evaluation (`ActivationInputs` for an executable input; `ReturnType` for an
executable return or return payload). These stay distinct typed dependencies
and distinct readiness changes; the shared prerequisite boundary alone is
atomic.

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
other exact event that triggered it. Each product pull has a checked, nonzero
id allocated monotonically by its retained session, and the producer-running pull carries that same id on
`evaluated`. Exclusive driver ownership and the producer's context-only API
make overlapping pulls impossible; cache requests do not invent evaluations.
Recursive search inside a producer stays within that exact request boundary.
Causality is never inferred from an aggregate or merely adjacent log lines.
Cyclic products use the same pending-product graph. `ExecutableEffects(E)` is
one ordinary formula over `MaterializedExecutable(E)` and the exact
`ExecutableEffects(callee)` products named by its local call edges. A pending
back-edge lets the generic group query identify the members; idempotent effect
union gives every member the join of the group's local and settled external
inputs without another traversal or fixpoint. `RuntimeDemand(E)` is not a
product and never enters this graph; its exact World-fact dependencies converge
through ordinary content-changing wakes. Recursive
`CallableConstruction(position)` products settle their position groups from
external anchors. `TransportShape(position)` has no
group: it cuts its own recursion from `CallGraphComponent` and `StaticCallees`
facts at recipe construction, so its evaluation is a function of settled facts
and of products that can settle without it. Component membership answers
mutual reachability, which is an equality; a grounded closure-call edge has no
static edge of its own. The group query records the prospective
`current -> dependency` read before borrowing the dependency map, so no graph
copy precedes the one Tarjan traversal that both detects a cycle and returns
the component containing the dependency. It follows the dependencies
of freshly evaluated formulas that completed with unresolved waits and visits
each reachable product once. The current evaluation supplies its reads
directly; every non-current group member therefore has a pending snapshot by
construction. A displaced product's last settled dependencies are retained for
reproduction, not treated as evidence that its new formula is waiting in the
cycle. As an executable-effects formula records its direct callee reads, its
pending component can only grow; it stages the last detected group after the
complete local read set. Hash order may change visitation order, but not the
search counts or component selected from one graph. A settled product answers
a read with the value it already holds, so it waits on nothing and no cycle of
waits runs through it — and a settled product never depends on an unsettled
one, so nothing is missed by not stepping into it.
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
Large product answers are single-threaded `Rc` values: the producer, memo entry,
downstream product, direct consumer, and cache hit retain one immutable
allocation. `PullSession` and `World` already contain
`Rc`-owned facts and never cross a `Send` boundary, so `Arc` would add atomic
traffic without adding a valid ownership path. Recursive-group members also
retain one `Rc<ProductDependencies>` because their validated external snapshot
is one value. Equality remains structural at both seams: a separately allocated
equal answer preserves its product generation, while changed content advances
it. Same-handle comparisons short-circuit on typed pointer identity before the
structural fallback, so ordinary memo handoffs do not rescan payloads.
When a producer reconstructs equal content, settlement retains the memo's
existing allocation, so the direct pull result cannot replace it with an
equal-but-distinct handle. `ProductMemo` is also the typed settled inventory:
its materialized, ABI, and symbolic-backend point queries and iterators project
the stored key/value pairs directly. `PullSession` carries no parallel artifact
maps.
Every member of a settled group retains the union of the
group's external product and fact dependencies when every duplicate dependency
state agrees; a mixed-generation or mixed-fact-state snapshot publishes nothing
and retries from fresh reads. Internal back-edges disappear only after that
concordance check. Product or fact movement, including dirtiness propagated
through a still-produced dependency, discards pending reader snapshots and
unregisters their edges before retry. Settled readers remain memoized and carry
that dirtiness lazily until requested. Equal reproduction preserves its
generation. Fact waits are satisfied at the Compiler2 front door by driving
only the direct fact producer needed for that exact fact, while deferring
forbidden root artifact jobs for the submitted root.

`PullSession` owns one root's retained product memo and scheduling relations
for that root's lifetime in `Compiler2`. A `TransportShape(position)` answer remains in its
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
`DeriveRuntimeDemand(E)` publishes exact input-source contributions into
`IncomingInputSlot(slot)` facts. `ContributionMap` joins each slot's sources
with the scheduler's publisher frontier governing replacement and withdrawal.
The target formula claims empty own slots, making absence of incoming edges
an authoritative readable answer. Callable construction reads that one settled
fact directly and consumes its immutable, typed-sorted source slice. Its slot
and shape prerequisites are named together. Equal publication retains the
joined allocation and revision.
`RuntimeDemand(E)` is an ordinary replacing World fact. Its formula records
current reads of exact direct and construction targets, then reads only those
targets' `RuntimeDemandInputs(E)` sub-facts. The sub-fact projects the input
vector from the same stored demand value while carrying its own revision, so a
return-only change cannot wake an input-only reader. Artifact products read the
full demand fact at settled readiness and use the normal fact-generation
dependency path for invalidation.

`Compiler2` retains one `PullSession` per root. Its memo emits a subscription
change exactly when the first reader of a fact appears or the last disappears.
A Compiler2-owned `FactKey -> roots` index routes each job-completion or
quiescence movement only to those roots. Dormant sessions receive it directly;
roots paused around a nested macro drive receive it once in an active inbox.
Repeated movements of one fact coalesce to the final `FactState` before the
next pull. This path scans neither roots, facts, products, nor dependencies,
and equal final state leaves readers settled.

Root requests reconcile queued source work before reading retained products. An
empty agenda costs O(1); queued work follows ordinary FIFO execution and exact
wakes. A request does not expand unrelated standing activation demand. Fatal or
timed-out reconciliation rejects the request because edit visibility is incomplete.

Scheduler dependencies have two typed identities: World facts and root-owned
products. The dependency index owns reads, waits, and finality for both. Fact
slots store only World fact revisions; an external state provider reads product
generations and readiness directly from the retained ProductMemo. A product has
no scheduler publisher, fact slot, or synthetic job.

A source job expanding a macro reads RootBackendContent of its hidden macro
root. Missing content becomes an exact product wait. Fact movement reaches only
subscribed root sessions. When it dirties a product with scheduler consumers,
the product movement makes those consumers unfinal through the ordinary
scheduler. The shared drive validates named product requests before fact
quiescence. Equal reproduction restores readiness without executing a Current
reader; changed generation reruns its exact source readers. The scheduler is
the sole owner of these read/wait edges; the product demand queue contains only
addresses to validate.

Retained sessions remain reachable while active. Short checked borrows end
before scheduler execution, so a nested macro root can read the same product
state authority without copying it or recursively borrowing an active drive.
Session activation identities persist across requests, while product request
ids advance. Each activation owns its work-start delta; nested roots and
standalone drives have separate balanced accounting boundaries.

RootBackendProductAnswer owns transport metadata and a shared BackendProgram.
ProductMemo retains the existing inner program allocation when backend content
reproduces equal, including when transport changes independently. This makes
RootBackendContent equality an O(1) pointer comparison. NativeProgram and macro
execution consume that same content handle. A native failure installs no native
answer and restores the same retained session for retry.

Compiler2::retire_root_products removes the root-owned fact subscription edges
and drops its memo. For products with scheduler consumers it also publishes the
exact dependency withdrawal through the scheduler. Existing consumer demand
survives even when a never-produced product has no withdrawal movement: the
next drive re-observes the exact requested address in a fresh memo. Retirement
allocates no replacement session, and removing the consumer cancels its demand.
Pending product requests reuse the scheduler's deduplicating FIFO `Agenda`;
renewed demand cannot revive a duplicate stale queue entry.
World holds no backend or macro artifact
payload that could retain the allocation or substitute a second authority.

### Root-local struct schemas

Each pruned `MaterializedExecutable` carries the typed `ModuleId`s of structs
its surviving construction/assertion steps or retained runtime type surfaces
name. A struct is one map-DNF leaf whose `MapTag::Struct(ModuleId, name)` and
fields remain conjunctive through every type operation. It is not recovered
from `Ty` display/canonical text or the old `impl-target::` string convention.
The artifact also drops `value_types`
for values removed by control pruning before it walks those surfaces, so dead
types cannot overpackage a schema.
`RootBackendProduct` unions those sets across its exact reachable executable
closure, reads each `StructDefined(module)` through `ProductReadContext`, and
only then materializes the runtime name-to-fields map. The map remains the
single interpreter/native/AOT schema input, but its membership and invalidation
are root-local and fact-tracked. No product snapshots `StructDefMap`, and a
struct reached only by another root cannot make retained and fresh calculations
disagree. `ModuleMap::reference_named` interns one `ModuleId` per fully
qualified name; the map tag compares that id, while runtime registration and
artifact rendering keep the full stable name (so `A.Item` and `B.Item` cannot
collide).
Record-axis top ranges over plain maps and every struct family; `map_top` is the
distinct positive `Plain {}` leaf. Runtime test envelopes preserve a struct tag
while erasing its unobservable positive field predicates, so `not Foo` rejects
a registered `Foo` while admitting a plain map and other values. Shaped raw
negatives conservatively keep the untestable family residue. An explicit `Foo
| map` admits both.

The cofinite named-struct predicates remain complete for the values a root can
observe: spawned processes use the same root program, while macro roots execute
separately over quoted values. If runtime values later cross independently
compiled roots, that feature must explicitly compose their schema sets.

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
