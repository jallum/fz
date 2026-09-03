//! Work loop and shared work vocabulary.
//!
//! This module owns the scheduler-facing shapes: job ids, fact ids, job
//! effects, and the drive loop. Concrete job implementations live under
//! `compiler2::jobs`.

use std::time::{Duration, Instant};

use crate::telemetry::{RawSpanGuard, RawSpanStop1 as _, RawSpanStop2, RawSpanTelemetry, TelemetryExt};

use super::code::CodeId;
use super::facts::{ClaimShape, DerivationId, FactUse};
use super::identity::{ActivationKey, ExecutableKey, FunctionId, ModuleId, RootId, TypeName};
use super::scheduler::{DriveOutcome, Scheduler, WorkStartReason};
use super::semantic::{CallSiteKey, StableSortKey};
use super::types::Types;
use super::world::World;

pub(crate) struct ExecutionContext<'a, T: crate::telemetry::Telemetry> {
    pub(crate) world: &'a mut World,
    pub(crate) telemetry: &'a T,
}

impl<'a, T: crate::telemetry::Telemetry> ExecutionContext<'a, T> {
    pub(crate) fn new(world: &'a mut World, telemetry: &'a T) -> Self {
        Self { world, telemetry }
    }

    pub(crate) fn complete_job(&mut self, job: Job, effects: JobEffects) -> super::JobCompletion {
        let completion = self.world.complete_job(job, effects);
        self.emit_job_completion(&completion);
        self.emit_activation_input_budget_collapses();
        completion
    }

    /// Report the correlated-input row sets this completion widened to their
    /// column-wise join because they crossed `ACTIVATION_INPUT_ROW_BUDGET`
    /// (fz-0xp).
    ///
    /// A collapse throws away the correlation its publishers took the trouble
    /// to keep, so one wide activation key stands where several narrow ones
    /// would have; it is the compiler's own admission that it is specializing
    /// on accumulated history rather than on the program. Since fz-kdt.106
    /// absorbed the ascent ladders the corpus produces none of these, which is
    /// what makes a single event worth reading.
    fn emit_activation_input_budget_collapses(&mut self) {
        let collapses = self.world.take_activation_input_collapses();
        if collapses == 0 {
            return;
        }
        self.telemetry.dispatch(
            &["fz", "compiler2", "activation_inputs", "budget_collapsed"],
            &crate::measurements! { collapses: collapses },
            &crate::telemetry::Metadata::new(),
        );
    }

    fn emit_job_completion(&self, completion: &super::world::JobCompletion) {
        if !completion.activation_input_changed.is_empty() {
            self.telemetry.raw_event2(
                &["fz", "compiler2", "activation_inputs", "defined"],
                &*self.world,
                completion,
            );
        }
        self.telemetry
            .raw_event2(&["fz", "compiler2", "work_graph", "applied"], &*self.world, completion);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Job {
    IndexCode(CodeId),
    ScopeCode(CodeId),
    DefineModule(ModuleId),
    DefineModuleInterface(ModuleId),
    PublishFunctionSource(FunctionId),
    ExpandFunctionSource(FunctionId),
    DefineFunction(FunctionId),
    DeriveTypeDef(TypeName),
    DeriveFunctionContract(FunctionId),
    LowerFunction(FunctionId),
    ReifyGuardDispatch(FunctionId),
    PlanEntryDispatch(FunctionId),
    BuildMacroExecutable(FunctionId),
    DeriveStaticCallees(FunctionId),
    DeriveCallGraphComponent(FunctionId),
    DeriveDispatchMask(FunctionId),
    SeedRoot(RootId),
    SeedActivation(ActivationKey),
    AnalyzeActivation(ActivationKey),
    DeriveExecutableFacts(ExecutableKey),
    BuildBackendProduct(RootId),
    LowerNativeProgram(RootId),
}

impl StableSortKey<Types> for Job {
    /// Every variant but `SeedActivation`/`AnalyzeActivation` carries only
    /// ids assigned by deterministic parse/scope traversal (`CodeId`,
    /// `ModuleId`, `FunctionId`, `RootId`), so their `Debug` text is already a
    /// stable key. Those two carry an `ActivationKey`, whose `arrow` is a bare
    /// interned `Ty` — rendered through `Types::display` instead of `{:?}` so
    /// the key does not depend on which run happened to intern it first.
    fn stable_sort_key(&self, types: &Types) -> String {
        match self {
            Job::SeedActivation(key) => format!("SeedActivation({})", key.stable_sort_key(types)),
            Job::AnalyzeActivation(key) => format!("AnalyzeActivation({})", key.stable_sort_key(types)),
            Job::DeriveExecutableFacts(key) => {
                format!("DeriveExecutableFacts({})", key.stable_sort_key(types))
            }
            other => format!("{other:?}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FactKey {
    CodeIndexed(CodeId),
    CodeScoped(CodeId),
    ModuleIndexed(ModuleId),
    ModuleDefined(ModuleId),
    ModuleInterface(ModuleId),
    FunctionSource(FunctionId),
    FunctionSourceStash(FunctionId),
    ExpandedFunctionSource(FunctionId),
    TypeDefined(TypeName),
    StructDefined(ModuleId),
    ProtocolDispatch(ModuleId),
    ProtocolImplProviders(ModuleId),
    FunctionDefined(FunctionId),
    FunctionContract(FunctionId),
    LoweredBody(FunctionId),
    GuardDispatch(FunctionId),
    EntryDispatch(FunctionId),
    MacroExecutable(FunctionId),
    StaticCallees(FunctionId),
    CallGraphComponent(FunctionId),
    Recursive(FunctionId),
    DispatchMask(FunctionId),
    RootEntry(RootId),
    Activation(ActivationKey),
    ActivationInputs(ActivationKey),
    ActivationAnalyzed(ActivationKey),
    ReturnType(ActivationKey),
    CallSiteTargets(CallSiteKey),
    CallSiteSummary(CallSiteKey),
    Executable(ExecutableKey),
    ExecutableFacts(ExecutableKey),
    BackendProgram(RootId),
    NativeProgram(RootId),
}

impl ClaimShape for FactKey {
    /// The fixpoint-evidence facts whose stores maintain a monotone join: an
    /// activation's return ascends by union (`ActivationMap::define_return`), and
    /// its body-input evidence ascends by the cross-publisher widen
    /// (`ActivationInputMap`). Every other fact's content overwrites.
    fn is_cumulative(&self) -> bool {
        matches!(self, FactKey::ReturnType(_) | FactKey::ActivationInputs(_))
    }
}

pub type WorkGraph = Scheduler<Job, FactKey>;

/// One independently-keyed answer a job reached, beside the whole-body one.
/// `reads`/`outputs`/`changed` are that answer's alone, and `concluded` says
/// whether the run reached it before any block (see
/// `scheduler::DerivationEffects`). A job that reports none of these publishes
/// its whole body as one answer, which is what every job does today.
#[derive(Debug, Clone)]
pub(crate) struct JobDerivation {
    pub(crate) derivation: DerivationId,
    pub(crate) reads: Vec<FactUse<FactKey>>,
    pub(crate) outputs: Vec<FactKey>,
    pub(crate) changed: Vec<FactKey>,
    pub(crate) concluded: bool,
}

/// What one job run reports. The flat `reads`/`outputs`/`changed` fields are
/// the job's WHOLE-BODY answer — `DerivationId::SOLE` — and `waits` are the
/// job's, since a job blocks whole. `derivations` names further answers the
/// same run reached independently; leaving it empty (every job today) means
/// the whole body is one answer and the ledger behaves exactly as it did
/// before publisher identity was refined.
#[derive(Debug, Clone, Default)]
pub(crate) struct JobEffects {
    pub(crate) reads: Vec<FactUse<FactKey>>,
    pub(crate) waits: Vec<FactUse<FactKey>>,
    pub(crate) outputs: Vec<FactKey>,
    pub(crate) changed: Vec<FactKey>,
    pub(crate) activation_input_contributions: Vec<(ActivationKey, Vec<super::types::Ty>)>,
    pub(crate) derivations: Vec<JobDerivation>,
}

impl JobEffects {
    pub(crate) fn wait_on_current(fact: FactKey) -> Self {
        Self {
            waits: vec![FactUse::current(fact)],
            ..Self::default()
        }
    }
}

pub(crate) fn current_uses<F>(facts: impl IntoIterator<Item = F>) -> Vec<FactUse<F>> {
    facts.into_iter().map(FactUse::current).collect()
}

pub(crate) fn settled_uses<F>(facts: impl IntoIterator<Item = F>) -> Vec<FactUse<F>> {
    facts.into_iter().map(FactUse::settled).collect()
}

impl World {
    /// Expands a demanded fact to its single producer and demands that
    /// producer when a run could say something new.
    ///
    /// This map is the one legitimate mechanism for work to start absent a
    /// wake (northstar: pull-based): the wait names the fact, the fact names
    /// its producer, and the producer runs because something waits on its
    /// output — never because another job commanded it. Both the product
    /// drivers (a `PullWait::Fact` with an empty agenda) and the bare
    /// scheduler (`drive_until`'s demand-on-stall pass) consult it.
    ///
    /// Facts whose producers publish them only as a co-output of a broader
    /// job's conclusion (`ModuleIndexed`, `StructDefined`, `ProtocolDispatch`,
    /// `ProtocolImplProviders`, `Executable`, `BackendProgram`,
    /// `NativeProgram`, `FunctionSourceStash`) have no arm: their demand rides
    /// the mapped facts that gate the job that co-produces them. Every fact
    /// with a single sole-producing job gets an arm here, even when that job
    /// is also the blocked branch of a `wait_on_current(fact)` bare wait elsewhere —
    /// naming the producer once, in this map, is what keeps every such wait a
    /// pull instead of a job pushing another job by name.
    /// Returns how many producers were actually demanded. `reason` is the
    /// work-start attribution for the demanded producer job -- it names
    /// which standing-demand expansion drove this call (see
    /// `WorkStartReason`), not the fact->producer mapping itself, since the
    /// mapping is shared by every caller of this function.
    pub(crate) fn demand_fact_producer(&mut self, fact: &FactKey, reason: WorkStartReason) -> u64 {
        let job = match fact {
            FactKey::RootEntry(root) => Some(Job::SeedRoot(*root)),
            FactKey::FunctionDefined(function) => Some(Job::DefineFunction(*function)),
            FactKey::ModuleDefined(module) => Some(Job::DefineModule(*module)),
            // `StructDefined` publishes as `DefineModule`'s co-output
            // (`source_publish::publish_struct_def`), exactly like
            // `ModuleDefined` above — the first real waiter on this fact
            // (fz-rh2.17.5.6.10's `DeriveTypeDef` struct wait-loop) needs the
            // same producer mapping or it would stall forever with no wake
            // source.
            FactKey::StructDefined(module) => Some(Job::DefineModule(*module)),
            FactKey::TypeDefined(name) => Some(Job::DeriveTypeDef(name.clone())),
            FactKey::FunctionContract(function) => Some(Job::DeriveFunctionContract(*function)),
            FactKey::CodeIndexed(code) => Some(Job::IndexCode(*code)),
            FactKey::GuardDispatch(function) => Some(Job::ReifyGuardDispatch(*function)),
            FactKey::LoweredBody(function) => Some(Job::LowerFunction(*function)),
            FactKey::CodeScoped(code) => Some(Job::ScopeCode(*code)),
            FactKey::ModuleInterface(module) => {
                let module = *module;
                Some(
                    if self.module_has_source_state(module) || self.is_runtime_module(module) {
                        Job::DefineModule(module)
                    } else {
                        Job::DefineModuleInterface(module)
                    },
                )
            }
            FactKey::StaticCallees(function) => Some(Job::DeriveStaticCallees(*function)),
            // One walk over the edge facts answers both: `Job::
            // DeriveCallGraphComponent` publishes the component id and the
            // body keying that component decides.
            FactKey::CallGraphComponent(function) | FactKey::Recursive(function) => {
                Some(Job::DeriveCallGraphComponent(*function))
            }
            FactKey::DispatchMask(function) => Some(Job::DeriveDispatchMask(*function)),
            FactKey::EntryDispatch(function) => Some(Job::PlanEntryDispatch(*function)),
            FactKey::MacroExecutable(function) => Some(Job::BuildMacroExecutable(*function)),
            FactKey::FunctionSource(function) => Some(Job::PublishFunctionSource(*function)),
            FactKey::ExpandedFunctionSource(function) => Some(Job::ExpandFunctionSource(*function)),
            FactKey::Activation(activation) | FactKey::ActivationInputs(activation) => {
                self.seed_activation_producer(activation)
            }
            FactKey::ActivationAnalyzed(activation)
            | FactKey::ReturnType(activation)
            | FactKey::CallSiteTargets(CallSiteKey { activation, .. })
            | FactKey::CallSiteSummary(CallSiteKey { activation, .. }) => {
                let activation = activation.clone();
                let mut pokes = 0;
                if let Some(seed) = self.seed_activation_producer(&activation) {
                    pokes += self.demand_producer_if_needed(seed, fact, reason) as u64;
                }
                return pokes + self.demand_producer_if_needed(Job::AnalyzeActivation(activation), fact, reason) as u64;
            }
            FactKey::ExecutableFacts(executable) => Some(Job::DeriveExecutableFacts(executable.clone())),
            _ => None,
        };
        job.map(|job| self.demand_producer_if_needed(job, fact, reason) as u64)
            .unwrap_or(0)
    }

    /// `Job::SeedActivation` as this activation's existence producer, or `None`
    /// when the activation is not its to mint (fz-kdt.69.1).
    ///
    /// Seeding reconstructs an activation's inputs from the key's own arrow
    /// (`jobs::root::seed_activation`). That is the truth only where nothing
    /// else describes them: a root entry, or a key the runtime-demand frontier
    /// minted from a callable surface no analysis ever walked. Once
    /// `ActivationInputs(activation)` has a publisher, those inputs are that
    /// publisher's evidence -- a caller's call edge -- and re-minting them from
    /// the arrow would both fabricate the caller's contribution and undo the
    /// caller's own withdrawal of the key, so no retraction could ever stick.
    fn seed_activation_producer(&self, activation: &ActivationKey) -> Option<Job> {
        (!self.has_fact(&FactKey::ActivationInputs(activation.clone())))
            .then(|| Job::SeedActivation(activation.clone()))
    }

    fn demand_producer_if_needed(&mut self, job: Job, target_fact: &FactKey, reason: WorkStartReason) -> bool {
        if !self.work_graph.has_run(&job) {
            // Never run: no wake source exists yet, so only a fresh demand
            // can start it.
            self.work_graph.enqueue(job, reason);
            return true;
        }
        if self.work_graph.blocked(&job) {
            // The producer already ran and paused on waits: those standing
            // waits make it wake-reachable the moment its missing facts land,
            // and every missing fact is itself a blocked wait whose producer
            // the drain expansion demands. Re-demanding the paused job would
            // only re-run it into the same unsatisfied waits.
            //
            // This gates ahead of the rebase test on purpose (fz-kdt.62). The
            // rebase flag is cleared only by a CONCLUDING run, so a job that
            // pauses on the same wait every time it runs stays flagged for the
            // rest of the drive, and a rebase-first order re-enqueues it at
            // every single drain. Nothing is lost by skipping it:
            // `Scheduler::enqueue_dependents` never marks a job rebased
            // without enqueueing it in the same step, so the shifted ground
            // has already been offered to this job once — and what it did with
            // the offer was block.
            return false;
        }
        if self.work_graph.rebased(&job) {
            // Ground shifted since its last conclusion: its claims are
            // unsettled whether or not it names `target_fact`, so it must
            // re-run to re-derive them.
            self.work_graph.enqueue(job, reason);
            return true;
        }
        if self.work_graph.output_keys(&job).contains(target_fact) {
            // The producer claims the fact and its ground stands: a
            // re-run would republish byte-identically.
            return false;
        }
        // A producer that ran, concluded, and did not claim `target_fact`
        // holds a live subscription on every fact its conclusion read —
        // including ones absent at read time, since every producer reads
        // (rather than conditionally reads) the facts its conclusion
        // depends on. It re-runs through the graph's own wake the moment
        // `target_fact` appears; re-demanding it here would only repeat a
        // byte-identical run.
        false
    }

    /// Answers, at a drain, the exact settled questions something is actually
    /// asking: `facts`.
    ///
    /// Transitive finality is maintained by counting, and counting can never
    /// finalize a cycle — `Scheduler::settle_quiescent` carries the proof. At
    /// a drain the agenda decides instead: a locally clean cone holding no
    /// dirty fact cannot move, so it is final. This is demand-driven, not a
    /// sweep — nothing is arbitrated that nobody asked about — and the step it
    /// produces is stashed for the execution context to emit, so the wake it
    /// causes always has a movement on the public stream to name.
    pub(crate) fn settle_quiescent(&mut self, facts: &[FactKey]) {
        let step = self.work_graph.settle_quiescent(facts);
        self.note_quiescence_step(step);
    }

    /// The blocked waiters' own settled questions. The waiter index is a
    /// `HashMap`, so its iteration order is a per-process `RandomState`
    /// artifact; the drain is already a barrier holding the full candidate
    /// list, and ordering it by the keys' own `Ord` (pure data, no rendering)
    /// pins the arbitration order deterministically. The scan-shaped drain
    /// pass itself is fz-kdt.46's remaining target: the edge-triggered form
    /// arbitrates the exact wait a completion left standing instead.
    pub(crate) fn settle_quiescent_waits(&mut self) {
        let mut facts = self.work_graph.waited_settled_facts();
        facts.sort();
        self.settle_quiescent(&facts);
    }

    /// Expands every blocked waiter's missing fact to its producer through
    /// the fact->producer map. This is the drain-time pull: a blocked wait is
    /// a standing demand for the fact, and the fact names its single
    /// producer. A producer that is itself paused on waits is not re-demanded
    /// — its missing facts are themselves blocked waits, so chains expand one
    /// frontier per pass. Returns how many producers were demanded.
    ///
    /// *Which* facts get demanded is provably a set (the dedup below), but
    /// each demand enqueues its fact's producer job onto the same agenda, so
    /// the order these calls happen in decides the order those jobs actually
    /// run — and a job that observes another job's published fact can join
    /// it under a keep-first merge, so run order is not free to vary.
    /// `unresolved()` hands back its waits ordered by the fact's `Debug`
    /// rendering, so one fact's several uses arrive adjacent and dropping the
    /// repeats leaves each fact once, in that same order.
    pub(crate) fn demand_blocked_wait_producers(&mut self) -> u64 {
        let mut facts: Vec<FactKey> = self
            .work_graph
            .unresolved()
            .into_iter()
            .map(|wait| wait.fact.into_fact())
            .collect();
        facts.dedup();
        facts
            .into_iter()
            .map(|fact| self.demand_fact_producer(&fact, WorkStartReason::BlockedWaiterExpansion))
            .sum()
    }

    /// Expands the standing demand every published activation carries: an
    /// `Activation(key)` fact without a settled `ActivationAnalyzed(key)` is a
    /// standing demand for that activation's analysis. This includes root
    /// entries published by `SeedRoot` and caller-discovered callees published
    /// by semantic analysis. The expansion only ignites first-run analysis —
    /// the `has_run` check is load-bearing, not an optimization: a callee whose
    /// first run blocked (waiting on some other fact, never claiming
    /// `ActivationAnalyzed`) stays perpetually `rebased` while blocked, and
    /// `demand_fact_producer`'s rebased branch re-enqueues unconditionally on
    /// every call — without this guard a permanently blocked-but-rebased
    /// callee would be re-run every stall pass forever. Once a callee has
    /// run at all, its own read/wait subscriptions (an unresolved wait's
    /// fact is separately covered by `demand_blocked_wait_producers`) carry
    /// every later revision. Retires each such key from the frontier so the
    /// working set stays bounded. Returns how many analyses were demanded.
    pub(crate) fn demand_activation_frontier_analyses(&mut self) -> u64 {
        let mut demanded = 0_u64;
        let mut keys = self.activation_frontier_keys();
        // `activation_frontier` is a `HashSet<ActivationKey>` (`world.rs`):
        // its iteration order is `RandomState`-dependent. `AnalyzeActivation`
        // mints fresh `Ty` combinations (interned call-site arrows) as a side
        // effect of running, so demanding two ready activations in a
        // different relative order between runs mints their arrows in a
        // different relative order too. Sort by `StableSortKey`
        // (`Types::display`, not raw `Ty`/`{:?}`) so the demand order is a
        // function of the activations' own structure, not of which run's
        // hasher happened to bucket them first.
        keys.sort_by_cached_key(|key| key.stable_sort_key(self.types()));
        for key in keys {
            if self.work_graph.has_run(&Job::AnalyzeActivation(key.clone())) {
                self.retire_activation_frontier(&key);
                continue;
            }
            demanded +=
                self.demand_fact_producer(&FactKey::ActivationAnalyzed(key), WorkStartReason::ActivationFrontier);
        }
        demanded
    }

    /// Pops the next ready job, expanding the two standing demand sources when
    /// the agenda has drained: published root-entry/caller-discovered-callee
    /// activations and blocked waiters' fact->producer expansions. Every job
    /// loop (the bare drive and the product fact-wait loops) pulls through this,
    /// so first-run ignition is owned by the scheduler boundary, not by any
    /// job's follow-up.
    pub(crate) fn next_ready_job(&mut self) -> Option<Job> {
        if let Some(job) = self.work_graph.pop() {
            return Some(job);
        }
        self.settle_quiescent_waits();
        if let Some(job) = self.work_graph.pop() {
            return Some(job);
        }
        let ignited = self.demand_activation_frontier_analyses();
        if ignited > 0
            && let Some(job) = self.work_graph.pop()
        {
            return Some(job);
        }
        if self.demand_blocked_wait_producers() > 0 {
            return self.work_graph.pop();
        }
        None
    }
}

impl<T: RawSpanTelemetry> ExecutionContext<'_, T> {
    pub(crate) fn drive_for(&mut self, timeout: Option<Duration>) -> DriveOutcome<Job, FactKey> {
        let deadline = timeout.map(|limit| Instant::now() + limit);
        self.drive_until(deadline, timeout)
    }

    /// Runs queued jobs until the work graph has no ready work.
    ///
    /// Each job gets one telemetry span that closes with the job's raw effects
    /// borrowed in place; the applied graph step rides the separate
    /// `work_graph.applied` event that `complete_job` emits. A fatal job closes
    /// its span, closes the drive span as fatal, and stops the loop.
    #[cfg(test)]
    pub fn drive(&mut self) -> DriveOutcome<Job, FactKey> {
        self.drive_until(None, None)
    }

    fn drive_until(&mut self, deadline: Option<Instant>, timeout: Option<Duration>) -> DriveOutcome<Job, FactKey> {
        let ExecutionContext { world, telemetry } = self;
        let tel = *telemetry;
        world.clear_reported_warnings();
        let span = tel.raw_span0_1::<DriveOutcome<Job, FactKey>>(&["fz", "compiler2", "drive"]);
        let mut jobs_ran = 0_u64;
        // Facts whose producers were already demanded at a stall with no fact
        // change since: re-demanding them would re-run byte-identical jobs.
        // Any content change clears the set — shifted ground can make the same
        // demand productive again.
        let mut stall_demanded: std::collections::HashSet<FactKey> = std::collections::HashSet::new();
        let mut changed_since_stall = true;
        let outcome = 'outcome: {
            'drive: loop {
                while world.work_graph.pending_jobs() > 0 {
                    if deadline.is_some_and(|limit| Instant::now() >= limit) {
                        let pending_jobs = world.work_graph.pending_jobs();
                        emit_drive_timed_out(tel, &timeout);
                        world.clear_unresolved_diagnostics();
                        ExecutionContext::new(world, tel).flush_reported_warnings();
                        break 'outcome DriveOutcome::TimedOut { jobs_ran, pending_jobs };
                    }
                    let Some(job) = world.work_graph.pop() else {
                        break;
                    };
                    let job_span = start_job_span(tel, &job);
                    let result = super::jobs::run(&mut ExecutionContext::new(world, tel), &job);
                    match result {
                        Ok(effects) => {
                            jobs_ran += 1;
                            let completion = ExecutionContext::new(world, tel).complete_job(job, effects);
                            stop_job_span(job_span, world, &completion);
                            changed_since_stall |= !completion.changed.is_empty();
                        }
                        Err(_) => {
                            job_span.exception();
                            world.clear_unresolved_diagnostics();
                            ExecutionContext::new(world, tel).flush_reported_warnings();
                            break 'outcome DriveOutcome::Fatal { job };
                        }
                    }
                }
                // The agenda drained. Two standing demand sources remain, both
                // pulls: every published activation not yet analyzed demands its
                // own analysis (`demand_activation_frontier_analyses`), and every
                // blocked waiter's fact names its single producer through the
                // fact->producer map — the same expansion the product drivers
                // perform when a fact wait finds an empty agenda. Only a genuine
                // drain reaches this pass, so it is event-driven, never a
                // per-iteration sweep. Demanding producers is commutative for
                // *which* facts get a producer job enqueued, but not for the
                // *order* those jobs then run in — the agenda is a FIFO, and a
                // job that observes another's published fact can join it under
                // a keep-first merge, so the order this loop pokes producers in
                // is still observable downstream — which is why `unresolved()`
                // orders its waits by data rather than by map order.
                if std::mem::take(&mut changed_since_stall) {
                    stall_demanded.clear();
                }
                // The agenda is empty, so every settled question standing over
                // a quiesced cone can be answered now (fz-kdt.44). Doing it
                // before the demand expansions answers any settled questions
                // left by the work that just quiesced.
                world.settle_quiescent_waits();
                let mut producer_pokes = world.demand_activation_frontier_analyses();
                let unresolved = world.work_graph.unresolved();
                for wait in &unresolved {
                    if stall_demanded.insert(wait.fact.fact().clone()) {
                        producer_pokes +=
                            world.demand_fact_producer(wait.fact.fact(), WorkStartReason::BlockedWaiterExpansion);
                    }
                }
                if producer_pokes > 0 {
                    tel.raw_event2(
                        &["fz", "compiler2", "drive", "demand_on_stall"],
                        &producer_pokes,
                        &stall_demanded,
                    );
                }
                let quiesced = flush_quiescence(world, tel);
                if quiescence_woke_work(&quiesced) {
                    // The arbiter satisfied a standing settled wait: real work
                    // is queued, so this drain is not a stall however few
                    // producers it managed to demand.
                    changed_since_stall = true;
                    continue 'drive;
                }
                if producer_pokes == 0 {
                    // Nothing left to demand: either resolved, or a genuine stall.
                    break 'drive;
                }
            }
            if !world.work_graph.has_unresolved() {
                world.clear_unresolved_diagnostics();
                ExecutionContext::new(world, tel).flush_reported_warnings();
                DriveOutcome::Resolved
            } else {
                let waits = world.work_graph.unresolved();
                ExecutionContext::new(world, tel).emit_unresolved_diagnostics(&waits);
                ExecutionContext::new(world, tel).flush_reported_warnings();
                DriveOutcome::Unresolved { waits }
            }
        };
        span.stop1(&outcome);
        outcome
    }
}

/// Emits every drain-arbiter step `World` stashed, and hands them back.
///
/// A readiness movement that satisfies a waiter is the one wake with no job
/// completion behind it, so it gets its own public event — without it a woken
/// waiter's next evaluation would name no moved input (fz-kdt.34.6).
pub(super) fn flush_quiescence<T: RawSpanTelemetry>(
    world: &mut World,
    tel: &T,
) -> Vec<super::AppliedStep<Job, FactKey>> {
    let steps = world.take_quiescence_steps();
    for step in &steps {
        tel.raw_event1(&["fz", "compiler2", "work_graph", "quiesced"], step);
    }
    steps
}

/// Whether any of `steps` started work.
pub(super) fn quiescence_woke_work(steps: &[super::AppliedStep<Job, FactKey>]) -> bool {
    steps.iter().any(|step| !step.wakes.is_empty())
}

fn emit_drive_timed_out(tel: &impl crate::telemetry::Telemetry, timeout: &Option<Duration>) {
    tel.raw_event1(&["fz", "compiler2", "drive", "timed_out"], timeout);
}

pub(super) fn start_job_span<'a, T: RawSpanTelemetry>(
    tel: &'a T,
    job: &Job,
) -> <T as RawSpanTelemetry>::Span1_2<'a, Job, World, super::JobCompletion> {
    tel.raw_span1_2::<Job, World, super::JobCompletion>(&["fz", "compiler2", "job"], job)
}

pub(super) fn stop_job_span(
    span: impl RawSpanStop2<World, super::JobCompletion>,
    world: &World,
    completion: &super::JobCompletion,
) {
    span.stop2(world, completion);
}
