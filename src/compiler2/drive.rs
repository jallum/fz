//! Work loop and shared work vocabulary.
//!
//! This module owns the scheduler-facing shapes: job ids, fact ids, job
//! effects, and the drive loop. Concrete job implementations live under
//! `compiler2::jobs`.

use std::collections::HashSet;
use std::time::{Duration, Instant};

use crate::telemetry::{RawSpanGuard, RawSpanStop0, RawSpanStop1 as _, RawSpanTelemetry, TelemetryExt};

use super::code::SourceOwner;
use super::facts::{ClaimShape, FactUse, Publisher};
use super::identity::{ActivationKey, ExecutableKey, FunctionId, ModuleId, RootId, TypeName};
use super::pull::ProductKey;
use super::scheduler::{DriveOutcome, Scheduler, WorkStartReason};
use super::semantic::{CallSiteKey, CallableConstructionTargetKey, SemanticOrd};
use super::types::Types;
use super::world::World;

pub(crate) struct ExecutionContext<'a, T: crate::telemetry::Telemetry> {
    pub(crate) world: &'a mut World,
    pub(crate) telemetry: &'a T,
    pub(crate) product_sessions: Option<&'a mut super::pull::ProductSessions>,
}

impl<'a, T: crate::telemetry::Telemetry> ExecutionContext<'a, T> {
    pub(crate) fn new(world: &'a mut World, telemetry: &'a T) -> Self {
        Self::with_optional_product_sessions(world, telemetry, None)
    }

    pub(crate) fn with_product_sessions(
        world: &'a mut World,
        telemetry: &'a T,
        product_sessions: &'a mut super::pull::ProductSessions,
    ) -> Self {
        Self::with_optional_product_sessions(world, telemetry, Some(product_sessions))
    }

    pub(crate) fn with_optional_product_sessions(
        world: &'a mut World,
        telemetry: &'a T,
        product_sessions: Option<&'a mut super::pull::ProductSessions>,
    ) -> Self {
        Self {
            world,
            telemetry,
            product_sessions,
        }
    }

    pub(crate) fn complete_job(&mut self, job: Job, effects: JobEffects) -> super::JobCompletion {
        let completion = self.apply_completion(job, effects);
        self.emit_job_completion(&completion);
        self.emit_activation_input_budget_collapses();
        completion
    }

    fn apply_completion(&mut self, job: Job, effects: JobEffects) -> super::JobCompletion {
        let previous_products = self
            .world
            .work_graph
            .dependency_uses(&job)
            .iter()
            .filter_map(|usage| match usage.fact() {
                DependencyKey::Product(address) => Some(address.clone()),
                _ => None,
            })
            .collect::<std::collections::HashSet<_>>();
        let Some(sessions) = self.product_sessions.as_deref_mut() else {
            assert!(
                effects.product_reads.is_empty() && effects.product_waits.is_empty(),
                "product consumers require retained sessions"
            );
            return self.world.complete_job(job, effects);
        };
        for address in effects.product_reads.iter().chain(&effects.product_waits) {
            sessions.observe(address);
        }
        let completion = self.world.complete_job_with_external(job, effects, sessions);
        for address in previous_products {
            if !self
                .world
                .work_graph
                .has_dependency_consumers(&DependencyKey::Product(address.clone()))
            {
                sessions.unobserve(&address);
            }
        }
        self.publish_dependency_movements(&completion.step.movements);
        completion
    }

    pub(crate) fn publish_dependency_movements(&mut self, movements: &[super::facts::FactMovement<DependencyKey>]) {
        let Some(sessions) = self.product_sessions.as_deref_mut() else {
            return;
        };
        let mut pending = movements
            .iter()
            .filter_map(|movement| {
                movement.key.fact().map(|key| super::facts::FactMovement {
                    key: key.clone(),
                    state: movement.state,
                })
            })
            .collect::<Vec<_>>();
        while !pending.is_empty() {
            let changes = sessions.publish(self.telemetry, self.world.types(), &pending);
            if changes.is_empty() {
                break;
            }
            let (graph, types) = self.world.work_graph_and_types();
            let step = graph.apply_external_changes_ordered(changes, sessions, types);
            self.telemetry
                .raw_event1(&["fz", "compiler2", "work_graph", "dependencies_moved"], &step);
            pending = step
                .movements
                .into_iter()
                .filter_map(|movement| {
                    movement.key.fact().map(|key| super::facts::FactMovement {
                        key: key.clone(),
                        state: movement.state,
                    })
                })
                .collect();
        }
    }

    pub(crate) fn apply_product_changes(&mut self, changes: Vec<super::facts::FactChange<DependencyKey>>) {
        if changes.is_empty() {
            return;
        }
        let sessions = self
            .product_sessions
            .as_deref()
            .expect("product movement requires retained sessions");
        let (graph, types) = self.world.work_graph_and_types();
        let step = graph.apply_external_changes_ordered(changes, sessions, types);
        self.telemetry
            .raw_event1(&["fz", "compiler2", "work_graph", "dependencies_moved"], &step);
        self.publish_dependency_movements(&step.movements);
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
    IndexCode(SourceOwner),
    ScopeCode(SourceOwner),
    DefineModule(ModuleId),
    DefineModuleInterface(ModuleId),
    ExpandFunctionSource(FunctionId),
    DefineFunction(FunctionId),
    DeriveTypeDef(TypeName),
    DeriveFunctionContract(FunctionId),
    LowerFunction(FunctionId),
    ReifyGuardDispatch(FunctionId),
    PlanEntryDispatch(FunctionId),
    DeriveStaticCallees(FunctionId),
    DeriveRecursive(FunctionId),
    DeriveInputDemand(FunctionId),
    SeedRoot(RootId),
    SeedActivation(ActivationKey),
    AnalyzeActivation(ActivationKey),
    DeriveExecutableFacts(ExecutableKey),
    DeriveCallableConstructionTarget(CallableConstructionTargetKey),
    DeriveRuntimeDemand(ExecutableKey),
}

impl SemanticOrd<Types> for Job {
    fn semantic_cmp(&self, other: &Self, types: &Types) -> std::cmp::Ordering {
        job_order_rank(self)
            .cmp(&job_order_rank(other))
            .then_with(|| match (self, other) {
                (Job::IndexCode(left), Job::IndexCode(right)) => left.cmp(right),
                (Job::ScopeCode(left), Job::ScopeCode(right)) => left.cmp(right),
                (Job::DefineModule(left), Job::DefineModule(right)) => left.cmp(right),
                (Job::DefineModuleInterface(left), Job::DefineModuleInterface(right)) => left.cmp(right),
                (Job::ExpandFunctionSource(left), Job::ExpandFunctionSource(right)) => left.cmp(right),
                (Job::DefineFunction(left), Job::DefineFunction(right)) => left.cmp(right),
                (Job::DeriveTypeDef(left), Job::DeriveTypeDef(right)) => left.cmp(right),
                (Job::DeriveFunctionContract(left), Job::DeriveFunctionContract(right)) => left.cmp(right),
                (Job::DeriveInputDemand(left), Job::DeriveInputDemand(right)) => left.cmp(right),
                (Job::LowerFunction(left), Job::LowerFunction(right)) => left.cmp(right),
                (Job::ReifyGuardDispatch(left), Job::ReifyGuardDispatch(right)) => left.cmp(right),
                (Job::PlanEntryDispatch(left), Job::PlanEntryDispatch(right)) => left.cmp(right),
                (Job::DeriveStaticCallees(left), Job::DeriveStaticCallees(right)) => left.cmp(right),
                (Job::DeriveRecursive(left), Job::DeriveRecursive(right)) => left.cmp(right),
                (Job::SeedRoot(left), Job::SeedRoot(right)) => left.cmp(right),
                (Job::SeedActivation(left), Job::SeedActivation(right))
                | (Job::AnalyzeActivation(left), Job::AnalyzeActivation(right)) => left.semantic_cmp(right, types),
                (Job::DeriveExecutableFacts(left), Job::DeriveExecutableFacts(right))
                | (Job::DeriveRuntimeDemand(left), Job::DeriveRuntimeDemand(right)) => left.semantic_cmp(right, types),
                (Job::DeriveCallableConstructionTarget(left), Job::DeriveCallableConstructionTarget(right)) => {
                    left.semantic_cmp(right, types)
                }
                _ => std::cmp::Ordering::Equal,
            })
    }
}

fn job_order_rank(job: &Job) -> u8 {
    match job {
        Job::AnalyzeActivation(_) => 0,
        Job::DefineFunction(_) => 3,
        Job::DefineModule(_) => 4,
        Job::DefineModuleInterface(_) => 5,
        Job::DeriveRecursive(_) => 6,
        Job::DeriveExecutableFacts(_) => 7,
        Job::DeriveFunctionContract(_) => 8,
        Job::DeriveInputDemand(_) => 9,
        Job::DeriveStaticCallees(_) => 10,
        Job::DeriveTypeDef(_) => 11,
        Job::ExpandFunctionSource(_) => 12,
        Job::IndexCode(_) => 13,
        Job::LowerFunction(_) => 14,
        Job::PlanEntryDispatch(_) => 15,
        Job::ReifyGuardDispatch(_) => 17,
        Job::ScopeCode(_) => 18,
        Job::SeedActivation(_) => 19,
        Job::SeedRoot(_) => 20,
        Job::DeriveCallableConstructionTarget(_) => 21,
        Job::DeriveRuntimeDemand(_) => 22,
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FactKey {
    CodeIndexed(SourceOwner),
    CodeScoped(SourceOwner),
    ModuleIndexed(ModuleId),
    ModuleDefined(ModuleId),
    ModuleInterface(ModuleId),
    FunctionSource(FunctionId),
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
    StaticCallees(FunctionId),
    Recursive(FunctionId),
    InputDemand(FunctionId),
    RootEntry(RootId),
    Activation(ActivationKey),
    ActivationInputs(ActivationKey),
    ActivationAnalyzed(ActivationKey),
    ReturnType(ActivationKey),
    CallSiteTargets(CallSiteKey),
    CallSiteSummary(CallSiteKey),
    Executable(ExecutableKey),
    ExecutableFacts(ExecutableKey),
    CallableConstructionTarget(CallableConstructionTargetKey),
    RuntimeDemandInput(ExecutableKey),
    RuntimeDemand(ExecutableKey),
    RuntimeDemandInputs(ExecutableKey),
    IncomingInputSlot(super::incoming_inputs::InputSlot),
}

impl SemanticOrd<Types> for FactKey {
    fn semantic_cmp(&self, other: &Self, types: &Types) -> std::cmp::Ordering {
        fact_diagnostic_rank(self)
            .cmp(&fact_diagnostic_rank(other))
            .then_with(|| self.cmp_same_variant(other, types))
    }
}

impl FactKey {
    /// A plain-English name for this fact's kind, for the rare fallback
    /// text that names a wait `World::unresolved_issue` did not turn into a
    /// diagnostic. Never the fact's own `Debug` form: that dumps internal
    /// ids (`ExecutableKey { .. }`, `ModuleId(3)`) that name nothing any
    /// source line wrote.
    pub(crate) fn kind_label(&self) -> &'static str {
        match self {
            FactKey::CodeIndexed(_) => "a source unit's index",
            FactKey::CodeScoped(_) => "a source unit's scope",
            FactKey::ModuleIndexed(_) => "a module's index",
            FactKey::ModuleDefined(_) => "a module definition",
            FactKey::ModuleInterface(_) => "a module's interface",
            FactKey::FunctionSource(_) => "a function's source",
            FactKey::ExpandedFunctionSource(_) => "a function's expanded source",
            FactKey::TypeDefined(_) => "a type definition",
            FactKey::StructDefined(_) => "a struct definition",
            FactKey::ProtocolDispatch(_) => "a protocol's dispatch",
            FactKey::ProtocolImplProviders(_) => "a protocol's implementation providers",
            FactKey::FunctionDefined(_) => "a function definition",
            FactKey::FunctionContract(_) => "a function's contract",
            FactKey::LoweredBody(_) => "a function's lowered body",
            FactKey::GuardDispatch(_) => "a function's guard dispatch",
            FactKey::EntryDispatch(_) => "a function's entry dispatch",
            FactKey::StaticCallees(_) => "a function's static callees",
            FactKey::Recursive(_) => "a function's recursion analysis",
            FactKey::InputDemand(_) => "a function's input demand",
            FactKey::RootEntry(_) => "a root's entry point",
            FactKey::Activation(_) => "a call's activation",
            FactKey::ActivationInputs(_) => "a call's activation inputs",
            FactKey::ActivationAnalyzed(_) => "a call's activation analysis",
            FactKey::ReturnType(_) => "a call's return type",
            FactKey::CallSiteTargets(_) => "a call site's targets",
            FactKey::CallSiteSummary(_) => "a call site's summary",
            FactKey::Executable(_) => "an executable",
            FactKey::ExecutableFacts(_) => "an executable's facts",
            FactKey::CallableConstructionTarget(_) => "a callable's construction target",
            FactKey::RuntimeDemandInput(_) => "an executable's runtime-demand input",
            FactKey::RuntimeDemand(_) => "an executable's runtime demand",
            FactKey::RuntimeDemandInputs(_) => "an executable's runtime-demand inputs",
            FactKey::IncomingInputSlot(_) => "an incoming input slot",
        }
    }

    fn cmp_same_variant(&self, other: &Self, types: &Types) -> std::cmp::Ordering {
        match (self, other) {
            (FactKey::CodeIndexed(left), FactKey::CodeIndexed(right))
            | (FactKey::CodeScoped(left), FactKey::CodeScoped(right)) => left.cmp(right),
            (FactKey::ModuleIndexed(left), FactKey::ModuleIndexed(right))
            | (FactKey::ModuleDefined(left), FactKey::ModuleDefined(right))
            | (FactKey::ModuleInterface(left), FactKey::ModuleInterface(right))
            | (FactKey::StructDefined(left), FactKey::StructDefined(right))
            | (FactKey::ProtocolDispatch(left), FactKey::ProtocolDispatch(right))
            | (FactKey::ProtocolImplProviders(left), FactKey::ProtocolImplProviders(right)) => left.cmp(right),
            (FactKey::FunctionSource(left), FactKey::FunctionSource(right))
            | (FactKey::ExpandedFunctionSource(left), FactKey::ExpandedFunctionSource(right))
            | (FactKey::FunctionDefined(left), FactKey::FunctionDefined(right))
            | (FactKey::FunctionContract(left), FactKey::FunctionContract(right))
            | (FactKey::LoweredBody(left), FactKey::LoweredBody(right))
            | (FactKey::GuardDispatch(left), FactKey::GuardDispatch(right))
            | (FactKey::EntryDispatch(left), FactKey::EntryDispatch(right))
            | (FactKey::StaticCallees(left), FactKey::StaticCallees(right))
            | (FactKey::InputDemand(left), FactKey::InputDemand(right))
            | (FactKey::Recursive(left), FactKey::Recursive(right)) => left.cmp(right),
            (FactKey::TypeDefined(left), FactKey::TypeDefined(right)) => left.cmp(right),
            (FactKey::IncomingInputSlot(left), FactKey::IncomingInputSlot(right)) => left.semantic_cmp(right, types),
            (FactKey::RootEntry(left), FactKey::RootEntry(right)) => left.cmp(right),
            (FactKey::Activation(left), FactKey::Activation(right))
            | (FactKey::ActivationInputs(left), FactKey::ActivationInputs(right))
            | (FactKey::ActivationAnalyzed(left), FactKey::ActivationAnalyzed(right))
            | (FactKey::ReturnType(left), FactKey::ReturnType(right)) => left.semantic_cmp(right, types),
            (FactKey::CallSiteTargets(left), FactKey::CallSiteTargets(right))
            | (FactKey::CallSiteSummary(left), FactKey::CallSiteSummary(right)) => left.semantic_cmp(right, types),
            (FactKey::CallableConstructionTarget(left), FactKey::CallableConstructionTarget(right)) => {
                left.semantic_cmp(right, types)
            }
            (FactKey::Executable(left), FactKey::Executable(right))
            | (FactKey::ExecutableFacts(left), FactKey::ExecutableFacts(right))
            | (FactKey::RuntimeDemandInput(left), FactKey::RuntimeDemandInput(right))
            | (FactKey::RuntimeDemand(left), FactKey::RuntimeDemand(right))
            | (FactKey::RuntimeDemandInputs(left), FactKey::RuntimeDemandInputs(right)) => {
                left.semantic_cmp(right, types)
            }
            _ => std::cmp::Ordering::Equal,
        }
    }
}

fn fact_diagnostic_rank(fact: &FactKey) -> u8 {
    match fact {
        FactKey::Activation(_) => 0,
        FactKey::ActivationAnalyzed(_) => 1,
        FactKey::ActivationInputs(_) => 2,
        FactKey::CallSiteSummary(_) => 5,
        FactKey::CallSiteTargets(_) => 6,
        FactKey::CallableConstructionTarget(_) => 36,
        FactKey::CodeIndexed(_) => 7,
        FactKey::CodeScoped(_) => 8,
        FactKey::EntryDispatch(_) => 9,
        FactKey::Executable(_) => 10,
        FactKey::ExecutableFacts(_) => 11,
        FactKey::ExpandedFunctionSource(_) => 12,
        FactKey::FunctionContract(_) => 13,
        FactKey::FunctionDefined(_) => 14,
        FactKey::FunctionSource(_) => 15,
        FactKey::GuardDispatch(_) => 17,
        FactKey::InputDemand(_) => 18,
        FactKey::LoweredBody(_) => 19,
        FactKey::ModuleDefined(_) => 21,
        FactKey::ModuleIndexed(_) => 22,
        FactKey::ModuleInterface(_) => 23,
        FactKey::ProtocolDispatch(_) => 24,
        FactKey::ProtocolImplProviders(_) => 25,
        FactKey::Recursive(_) => 26,
        FactKey::ReturnType(_) => 27,
        FactKey::RootEntry(_) => 28,
        FactKey::StaticCallees(_) => 29,
        FactKey::StructDefined(_) => 30,
        FactKey::TypeDefined(_) => 31,
        FactKey::RuntimeDemand(_) => 32,
        FactKey::RuntimeDemandInput(_) => 33,
        FactKey::RuntimeDemandInputs(_) => 34,
        FactKey::IncomingInputSlot(_) => 37,
    }
}

impl ClaimShape for FactKey {
    /// The fixpoint-evidence facts whose stores maintain a monotone join: an
    /// activation's return ascends by union (`ActivationMap::define_return`), and
    /// its body-input evidence ascends by the cross-publisher widen
    /// (`ActivationInputMap`). Every other fact's content overwrites.
    fn is_cumulative(&self) -> bool {
        matches!(
            self,
            FactKey::ReturnType(_)
                | FactKey::ActivationInputs(_)
                | FactKey::RuntimeDemandInput(_)
                | FactKey::IncomingInputSlot(_)
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProductAddress {
    pub(crate) root: RootId,
    pub(crate) key: ProductKey,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DependencyKey {
    Fact(FactKey),
    Product(ProductAddress),
}

impl DependencyKey {
    pub(crate) fn fact(&self) -> Option<&FactKey> {
        match self {
            Self::Fact(fact) => Some(fact),
            Self::Product(_) => None,
        }
    }
}

impl super::facts::ClaimShape for DependencyKey {
    fn is_cumulative(&self) -> bool {
        self.fact().is_some_and(super::facts::ClaimShape::is_cumulative)
    }
}

impl SemanticOrd<Types> for DependencyKey {
    fn semantic_cmp(&self, other: &Self, types: &Types) -> std::cmp::Ordering {
        match (self, other) {
            (Self::Fact(left), Self::Fact(right)) => left.semantic_cmp(right, types),
            (Self::Product(left), Self::Product(right)) => left
                .root
                .cmp(&right.root)
                .then_with(|| left.key.semantic_cmp(&right.key, types)),
            (Self::Fact(_), Self::Product(_)) => std::cmp::Ordering::Less,
            (Self::Product(_), Self::Fact(_)) => std::cmp::Ordering::Greater,
        }
    }
}

/// How a reader may use an answer right now: read a partner's answer as it
/// stands, read a concluded answer, or wait for the answer to conclude.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum AnswerUse {
    Partner(FactUse<FactKey>),
    Concluded(FactUse<FactKey>),
    Wait(FactUse<FactKey>),
}

/// One reader's accumulated use of the facts it consults while it runs:
/// every answer available to read, and every answer it must still wait for.
#[derive(Debug, Clone)]
pub(crate) struct UseCollector {
    reader: Job,
    reads: Vec<FactUse<FactKey>>,
    waits: HashSet<FactUse<FactKey>>,
}

impl UseCollector {
    pub(crate) fn new(reader: Job) -> Self {
        Self {
            reader,
            reads: Vec::new(),
            waits: HashSet::new(),
        }
    }

    pub(crate) fn read(&mut self, fact: FactKey) {
        self.reads.push(FactUse::current(fact));
    }

    pub(crate) fn wait(&mut self, fact: FactKey) {
        self.waits.insert(FactUse::current(fact));
    }

    /// Classifies `fact` through [`World::answer_use`] without recording it.
    pub(crate) fn classify(&self, world: &World, fact: FactKey) -> AnswerUse {
        world.answer_use(&self.reader, fact)
    }

    /// Records a read exactly as classified.
    pub(crate) fn record_read(&mut self, read: FactUse<FactKey>) {
        self.reads.push(read);
    }

    /// Records a wait exactly as classified.
    pub(crate) fn record_wait(&mut self, wait: FactUse<FactKey>) {
        self.waits.insert(wait);
    }

    pub(crate) fn answer(&mut self, world: &World, fact: FactKey) -> AnswerUse {
        let answer = self.classify(world, fact);
        match &answer {
            AnswerUse::Partner(read) | AnswerUse::Concluded(read) => self.record_read(read.clone()),
            AnswerUse::Wait(wait) => self.record_wait(wait.clone()),
        }
        answer
    }

    pub(crate) fn into_reads_waits(self) -> (Vec<FactUse<FactKey>>, HashSet<FactUse<FactKey>>) {
        (self.reads, self.waits)
    }

    /// Whether this run has registered any wait yet. Lets a job assert, at
    /// the moment it mints a value standing in for an awaited answer, that
    /// the wait which will wake it is already here.
    pub(crate) fn has_waits(&self) -> bool {
        !self.waits.is_empty()
    }
}

pub(crate) fn fact_dependency(fact: FactUse<FactKey>) -> FactUse<DependencyKey> {
    match fact {
        FactUse::Current(fact) => FactUse::current(DependencyKey::Fact(fact)),
        FactUse::Concluded(fact) => FactUse::concluded(DependencyKey::Fact(fact)),
        FactUse::Settled(fact) => FactUse::settled(DependencyKey::Fact(fact)),
    }
}

pub(crate) fn as_fact_use(usage: FactUse<DependencyKey>) -> Option<FactUse<FactKey>> {
    match usage {
        FactUse::Current(DependencyKey::Fact(fact)) => Some(FactUse::current(fact)),
        FactUse::Concluded(DependencyKey::Fact(fact)) => Some(FactUse::concluded(fact)),
        FactUse::Settled(DependencyKey::Fact(fact)) => Some(FactUse::settled(fact)),
        _ => None,
    }
}

/// Which answer of a job a claim belongs to. A job that answers one question
/// per run publishes every fact under `Job`. A job that answers several --
/// a scope walk gives one answer per function it reaches, an analysis one per
/// activation it contributes to -- names the key of each answer, and each
/// stands on exactly the reads that produced it.
///
/// The key is the question, never the position: a walk that stops earlier one
/// run and later the next must still name the same answers, or a re-run could
/// not replace what it re-derived nor retract what it no longer reaches.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub enum DerivationKey {
    /// The job's own answer -- the one its standing waits leave deriving.
    #[default]
    Job,
    Function(FunctionId),
    Activation(ActivationKey),
    Executable(ExecutableKey),
    InputSlot(super::incoming_inputs::InputSlot),
}

/// One answer a job gave. Reads, claims, cleanliness and finality are all
/// per answer; the agenda, standing waits and wakes are per job.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Derivation {
    pub job: Job,
    pub key: DerivationKey,
}

impl Derivation {
    pub(crate) fn of(job: Job, key: DerivationKey) -> Self {
        Self { job, key }
    }
}

impl Publisher for Derivation {
    type Run = Job;

    fn run(&self) -> &Job {
        &self.job
    }

    fn of_run(job: &Job) -> Self {
        Self {
            job: job.clone(),
            key: DerivationKey::Job,
        }
    }
}

impl SemanticOrd<Types> for Derivation {
    fn semantic_cmp(&self, other: &Self, types: &Types) -> std::cmp::Ordering {
        self.job
            .semantic_cmp(&other.job, types)
            .then_with(|| self.key.semantic_cmp(&other.key, types))
    }
}

impl SemanticOrd<Types> for DerivationKey {
    fn semantic_cmp(&self, other: &Self, types: &Types) -> std::cmp::Ordering {
        derivation_key_rank(self)
            .cmp(&derivation_key_rank(other))
            .then_with(|| match (self, other) {
                (DerivationKey::Function(left), DerivationKey::Function(right)) => left.cmp(right),
                (DerivationKey::Activation(left), DerivationKey::Activation(right)) => left.semantic_cmp(right, types),
                (DerivationKey::Executable(left), DerivationKey::Executable(right)) => left.semantic_cmp(right, types),
                (DerivationKey::InputSlot(left), DerivationKey::InputSlot(right)) => left.semantic_cmp(right, types),
                _ => std::cmp::Ordering::Equal,
            })
    }
}

fn derivation_key_rank(key: &DerivationKey) -> u8 {
    match key {
        DerivationKey::Job => 0,
        DerivationKey::Function(_) => 1,
        DerivationKey::Activation(_) => 2,
        DerivationKey::Executable(_) => 3,
        DerivationKey::InputSlot(_) => 4,
    }
}

pub type WorkGraph = Scheduler<Derivation, DependencyKey>;

/// One answer a job reached before its own conclusion: the facts it owns and
/// the ground it stood on when it reached them. Each is published as its own
/// derivation, so a run that blocks later cannot unsettle what it already
/// decided, and a reader of one answer never inherits the reads of another.
#[derive(Debug, Clone, Default)]
pub(crate) struct JobDerivation {
    pub(crate) key: DerivationKey,
    pub(crate) reads: Vec<FactUse<FactKey>>,
    pub(crate) product_reads: Vec<ProductAddress>,
    pub(crate) outputs: Vec<FactKey>,
    pub(crate) changed: Vec<FactKey>,
}

/// One job run: the answers it reached, and its own dependencies, owned facts
/// and contributions.
#[derive(Debug, Clone, Default)]
pub(crate) struct JobEffects {
    /// Actual RuntimeDemand body walks; prerequisite-only returns perform none.
    pub(crate) runtime_demand_evaluations: u64,
    /// The answers this run reached on the way to its own conclusion.
    pub(crate) derivations: Vec<JobDerivation>,
    pub(crate) reads: Vec<FactUse<FactKey>>,
    pub(crate) waits: Vec<FactUse<FactKey>>,
    pub(crate) product_reads: Vec<ProductAddress>,
    pub(crate) product_waits: Vec<ProductAddress>,
    pub(crate) outputs: Vec<FactKey>,
    pub(crate) changed: Vec<FactKey>,
    pub(crate) activation_input_contributions: Vec<(ActivationKey, Vec<super::types::Ty>)>,
    pub(crate) runtime_demand_input_contributions: Vec<(ExecutableKey, super::semantic::TargetDemandContribution)>,
    pub(crate) incoming_input_contributions:
        std::collections::HashMap<super::incoming_inputs::InputSlot, super::incoming_inputs::IncomingInputSources>,
    /// What the demand sent to each callee stands on, when that is less than
    /// everything the run read.
    pub(crate) send_reads: std::collections::HashMap<ExecutableKey, Vec<FactUse<FactKey>>>,
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
    /// A need starts its producer the moment it is recorded. `complete_job`
    /// is the one call site: once a run's outputs are applied, this demands
    /// each fact it still waits on, and the first analysis of every
    /// activation it published that has never run. Both lists are expanded
    /// in semantic order, never insertion order.
    ///
    /// Demanding here, inside the completion of one known job, is what keeps
    /// start order a pure function of history rather than of an unordered
    /// set's iteration: every demand happens in the semantic order of that
    /// one job's own waits and activations, the agenda is FIFO, so start
    /// order is a pure function of completion order, which is itself a pure
    /// function of the previous starts. No step ever consults a set whose
    /// iteration order is unspecified.
    pub(crate) fn demand_recorded_needs(&mut self, job: &Job, activations: Vec<ActivationKey>) {
        let mut waits: Vec<FactKey> = self
            .work_graph
            .waits_for(job)
            .into_iter()
            .filter_map(|wait| wait.fact().fact().cloned())
            .collect();
        waits.sort_by(|left, right| left.semantic_cmp(right, self.types()));
        waits.dedup();
        for fact in waits {
            self.demand_fact_producer(&fact, WorkStartReason::BlockedWaiterExpansion);
        }
        let mut activations = activations;
        activations.sort_by(|left, right| left.semantic_cmp(right, self.types()));
        activations.dedup();
        for key in activations {
            if !self.work_graph.has_run(&Job::AnalyzeActivation(key.clone())) {
                self.demand_fact_producer(&FactKey::ActivationAnalyzed(key), WorkStartReason::ActivationPublished);
            }
        }
    }

    /// Walks a blocked job's own standing waits, and the waits of any
    /// producer among them that is itself only blocked (not concluded or
    /// rebased), looking for the first wait whose producer never ran at
    /// all. That is the one kind of stale wait nothing else will ever ask
    /// about again: a failed run concludes nothing and leaves no record,
    /// so once it drops off the agenda it is gone unless something walks
    /// back to it. Each job is visited at most once, so a genuine cycle --
    /// two producers blocked on each other, such as a type definition
    /// recursive on itself -- is walked once and left exactly as blocked
    /// as it was, not retried forever. Returns how many producers were
    /// actually demanded.
    fn revive_blocked_chain(&mut self, job: &Job) -> u64 {
        let mut demanded = 0_u64;
        let mut visited = HashSet::from([job.clone()]);
        let mut frontier = vec![job.clone()];
        while let Some(current) = frontier.pop() {
            let mut waits: Vec<FactKey> = self
                .work_graph
                .waits_for(&current)
                .into_iter()
                .filter_map(|wait| wait.fact().fact().cloned())
                .collect();
            waits.sort_by(|left, right| left.semantic_cmp(right, self.types()));
            waits.dedup();
            for fact in waits {
                let Some(producer) = self.fact_producer(&fact) else {
                    continue;
                };
                if !self.work_graph.has_run(&producer) {
                    demanded += self.demand_fact_producer(&fact, WorkStartReason::GateExpansion);
                } else if self.work_graph.blocked(&producer) && visited.insert(producer.clone()) {
                    frontier.push(producer);
                }
            }
        }
        demanded
    }

    /// Parks a never-run job on its own missing gates instead of starting
    /// it: the job waits on each gate at the readiness `Job::missing_gates`
    /// named, and each gate's producer is demanded in the same breath, so
    /// the gate's own landing wakes this job the ordinary way. Returns how
    /// many producers were actually demanded.
    fn park_on_gates(&mut self, job: Job, gates: &[FactUse<FactKey>]) -> u64 {
        let uses = gates.iter().cloned().map(fact_dependency).collect();
        self.work_graph.wait_without_running(job, uses);
        gates
            .iter()
            .map(|gate| self.demand_fact_producer(gate.fact(), WorkStartReason::GateExpansion))
            .sum()
    }

    /// Expands a demanded fact to its single producer and demands that
    /// producer when a run could say something new.
    ///
    /// This map is the one legitimate mechanism for work to start absent a
    /// wake (northstar: pull-based): the wait names the fact, the fact names
    /// its producer, and the producer runs because something waits on its
    /// output — never because another job commanded it. `demand_recorded_needs`
    /// (a job's waits and published activations, at completion),
    /// `park_on_gates` (a never-run job's missing gates, at the moment it is
    /// popped), and the product pull's own fact-wait loop all consult it, each
    /// at the moment its own need is recorded — there is no drain-time sweep
    /// left that consults it on a timer.
    ///
    /// Facts whose producers publish them only as a co-output of a broader
    /// job's conclusion (`ModuleIndexed`, `StructDefined`, `ProtocolDispatch`,
    /// `ProtocolImplProviders`, `Executable`) have no arm: their demand rides
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
        match fact {
            // A function's source is published by the scope walk that defines
            // it, and which walk that is depends on where the function lives.
            // `demand_function_scope` names the scope facts that gate it, and
            // each of those has its own arm in `fact_producer`, so expanding
            // them is how this fact reaches its producer. A function no
            // submitted code names yet has no scope fact: nothing is demanded,
            // and the wait is discharged when some later walk publishes the
            // source. A corpus with two homes for one name is diagnosed by the
            // job that needs the source, not by this map, which carries no
            // telemetry.
            FactKey::FunctionSource(function) => {
                let scopes = self.demand_function_scope(*function).unwrap_or_default();
                scopes
                    .iter()
                    .map(|scope| self.demand_fact_producer(scope, reason))
                    .sum()
            }
            // An activation's analysis needs the activation to exist, so its
            // seed is demanded along with it.
            FactKey::ActivationAnalyzed(activation)
            | FactKey::ReturnType(activation)
            | FactKey::CallSiteTargets(CallSiteKey { activation, .. })
            | FactKey::CallSiteSummary(CallSiteKey { activation, .. }) => {
                let activation = activation.clone();
                let mut pokes = 0;
                if let Some(seed) = self.seed_activation_producer(&activation) {
                    pokes += self.demand_producer_if_needed(seed, fact, reason) as u64;
                }
                pokes + self.demand_producer_if_needed(Job::AnalyzeActivation(activation), fact, reason) as u64
            }
            _ => self
                .fact_producer(fact)
                .map(|job| self.demand_producer_if_needed(job, fact, reason) as u64)
                .unwrap_or(0),
        }
    }

    /// Whether `from` is waiting, directly or through the jobs it waits on,
    /// for an answer only `to` can give.
    ///
    /// A run that would wait on a job already waiting on it would close a
    /// cycle of waits that nothing can open: each is the other's missing
    /// answer. The walk follows standing waits to their producers and visits
    /// each job once.
    pub(crate) fn waits_reach(&self, from: &Job, to: &Job) -> bool {
        let mut pending = vec![from.clone()];
        let mut seen = HashSet::new();
        while let Some(job) = pending.pop() {
            if !seen.insert(job.clone()) {
                continue;
            }
            for wait in self.work_graph.waits_for(&job) {
                let Some(producer) = wait.fact().fact().and_then(|fact| self.fact_producer(fact)) else {
                    continue;
                };
                if &producer == to {
                    return true;
                }
                pending.push(producer);
            }
        }
        false
    }

    /// How `reader` may use the answer `fact` gives. A partner's answer, one
    /// whose producer is waiting on `reader`, is one fixpoint with the
    /// reader's own and is read however unfinished. Any other answer is read
    /// only once it has concluded, and waited for until then. The reader's
    /// own answer counts as a partner too: a self-recursive job's first run
    /// has registered no wait yet for `waits_reach` to find.
    pub(crate) fn answer_use(&self, reader: &Job, fact: FactKey) -> AnswerUse {
        let partner = self
            .fact_producer(&fact)
            .is_some_and(|producer| &producer == reader || self.waits_reach(&producer, reader));
        if partner {
            AnswerUse::Partner(FactUse::current(fact))
        } else if self.fact_is_concluded(&fact) {
            AnswerUse::Concluded(FactUse::concluded(fact))
        } else {
            AnswerUse::Wait(FactUse::concluded(fact))
        }
    }

    /// The next queued job worth running. This is the one door: a job
    /// missing a gate is parked on it instead of run (`Job::missing_gates`),
    /// and a job whose last run read a concluded answer that is now being
    /// derived again would find that answer missing and wait for it, so it
    /// waits without running too.
    pub(crate) fn pop_runnable(&mut self) -> Option<Job> {
        while let Some(job) = self.work_graph.pop() {
            let gates = job.missing_gates(self);
            if !gates.is_empty() {
                self.park_on_gates(job, &gates);
                continue;
            }
            let missing = self.concluded_answers_missing(&job);
            if missing.is_empty() {
                self.work_graph.record_run_start(&job);
                return Some(job);
            }
            self.work_graph.wait_without_running(job, missing);
        }
        None
    }

    /// A job woken on one of several standing waits must not run while
    /// another is still unanswered, or it would immediately re-park on the
    /// one it was never actually given.
    fn concluded_answers_missing(&self, job: &Job) -> HashSet<FactUse<DependencyKey>> {
        let concluded_facts = |uses: HashSet<FactUse<DependencyKey>>| {
            uses.into_iter().filter_map(|use_| match use_ {
                FactUse::Concluded(DependencyKey::Fact(fact)) => Some(fact),
                _ => None,
            })
        };
        concluded_facts(self.work_graph.reads(job))
            .chain(concluded_facts(self.work_graph.waits_for(job)))
            .filter_map(|fact| match self.answer_use(job, fact) {
                AnswerUse::Wait(wait) => Some(fact_dependency(wait)),
                AnswerUse::Partner(_) | AnswerUse::Concluded(_) => None,
            })
            .collect()
    }

    /// The job that publishes `fact`, when one job does.
    ///
    /// Facts whose producers publish them only as a co-output of a broader
    /// job's conclusion (`ModuleIndexed`, `StructDefined`, `ProtocolDispatch`,
    /// `ProtocolImplProviders`, `Executable`) have no arm: their demand rides
    /// the mapped facts that gate the job that co-produces them. A function's
    /// source has no single producer either; `demand_fact_producer` expands it
    /// through its scope facts.
    pub(crate) fn fact_producer(&self, fact: &FactKey) -> Option<Job> {
        match fact {
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
            FactKey::Recursive(function) => Some(Job::DeriveRecursive(*function)),
            FactKey::InputDemand(function) => Some(Job::DeriveInputDemand(*function)),
            FactKey::EntryDispatch(function) => Some(Job::PlanEntryDispatch(*function)),
            FactKey::ExpandedFunctionSource(function) => Some(Job::ExpandFunctionSource(*function)),
            FactKey::Activation(activation) | FactKey::ActivationInputs(activation) => {
                self.seed_activation_producer(activation)
            }
            FactKey::ActivationAnalyzed(activation)
            | FactKey::ReturnType(activation)
            | FactKey::CallSiteTargets(CallSiteKey { activation, .. })
            | FactKey::CallSiteSummary(CallSiteKey { activation, .. }) => {
                Some(Job::AnalyzeActivation(activation.clone()))
            }
            FactKey::ExecutableFacts(executable) => Some(Job::DeriveExecutableFacts(executable.clone())),
            FactKey::CallableConstructionTarget(key) => Some(Job::DeriveCallableConstructionTarget(key.clone())),
            FactKey::RuntimeDemand(executable) | FactKey::RuntimeDemandInputs(executable) => {
                Some(Job::DeriveRuntimeDemand(executable.clone()))
            }
            FactKey::IncomingInputSlot(slot) => Some(Job::DeriveRuntimeDemand(slot.executable.clone())),
            _ => None,
        }
    }

    /// `Job::SeedActivation` as this activation's existence producer, or `None`
    /// when the activation is not its to mint (fz-kdt.69.1).
    ///
    /// Seeding reconstructs an activation's inputs from the key's own arrow
    /// (`jobs::root::seed_activation`). That is the truth only for a key the
    /// runtime-demand frontier minted from a callable surface no analysis ever
    /// walked. `SeedRoot` owns root entries, and callers own the keys they
    /// discover. Once
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
            // Never run: only a demand can start it. A missing gate
            // redirects that demand to the gate's own producer instead
            // (`park_on_gates`), a different job than `job`, so it is
            // tallied under `GateExpansion` rather than this call's reason.
            let gates = job.missing_gates(self);
            if !gates.is_empty() {
                return self.park_on_gates(job, &gates) > 0;
            }
            self.work_graph.enqueue(job, reason);
            return true;
        }
        if self.work_graph.blocked(&job) {
            // Already blocked on standing waits that wake it the ordinary way
            // once those facts land -- but a wait's producer, or a producer
            // further down the same chain, can itself have failed and left
            // no record (a failed run concludes nothing, by design), in
            // which case nothing else will ever ask for it again. Chasing
            // down to the first never-run producer along this job's own
            // wait chain is the only remaining chance for a link that
            // silently died to be tried again; it is checked ahead of the
            // rebase case below because a job is never marked rebased
            // without being enqueued in the same step, so a blocked job
            // already saw its shifted ground and chose to wait.
            return self.revive_blocked_chain(&job) > 0;
        }
        if self.work_graph.rebased(&job) {
            // Ground shifted since its last conclusion: its claims are
            // unsettled whether or not it names `target_fact`, so it must
            // re-run to re-derive them.
            self.work_graph.enqueue(job, reason);
            return true;
        }
        if self
            .work_graph
            .output_keys(&job)
            .contains(&DependencyKey::Fact(target_fact.clone()))
        {
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
    /// a drain the agenda decides instead: a fact is certified only when no
    /// publisher in its transitive read ground is dirty and no external
    /// product beneath it is unsettled. The walk that proves this visits
    /// every unquiet fact in that ground and certifies all of them, since the
    /// same argument proved each one final. This is demand-driven, not a
    /// sweep — the walk starts only from `facts` and follows what they
    /// actually read — and the step it produces is stashed for the execution
    /// context to emit, so the wake it causes always has a movement on the
    /// public stream to name.
    pub(crate) fn settle_quiescent_with_sessions(
        &mut self,
        facts: &[FactKey],
        sessions: Option<&super::pull::ProductSessions>,
    ) {
        let (work_graph, types) = self.work_graph_and_types();
        let keys = facts.iter().cloned().map(DependencyKey::Fact).collect::<Vec<_>>();
        let step = match sessions {
            Some(sessions) => work_graph.settle_quiescent_ordered_with_external(&keys, sessions, types),
            None => work_graph.settle_quiescent_ordered(&keys, types),
        };
        self.note_quiescence_step(step);
    }

    /// The blocked waiters' own settled questions. The waiter index is a
    /// `HashMap`, so its iteration order is a per-process `RandomState`
    /// artifact; the drain is already a barrier holding the full candidate
    /// list, and ordering it by the keys' own `Ord` (pure data, no rendering)
    /// pins the arbitration order deterministically. The scan-shaped drain
    /// pass itself is fz-kdt.46's remaining target: the edge-triggered form
    /// arbitrates the exact wait a completion left standing instead.
    pub(crate) fn settle_quiescent_waits(&mut self, sessions: Option<&super::pull::ProductSessions>) {
        let mut facts = self
            .work_graph
            .waited_settled_facts()
            .into_iter()
            .filter_map(|key| key.fact().cloned())
            .collect::<Vec<_>>();
        facts.sort_by(|left, right| left.semantic_cmp(right, self.types()));
        self.settle_quiescent_with_sessions(&facts, sessions);
    }

    /// Pops the next ready job, settling quiescent waits once if the agenda
    /// has drained. Every job loop (the bare drive and the product fact-wait
    /// loops) pulls through this. There is no demand expansion left to do
    /// here: a need starts its producer when it is recorded
    /// (`demand_recorded_needs`, `park_on_gates`), never when the agenda
    /// happens to run dry, so a drain only arbitrates the settled questions
    /// standing over quiesced ground -- it starts nothing.
    pub(crate) fn next_ready_job(&mut self, sessions: Option<&super::pull::ProductSessions>) -> Option<Job> {
        if let Some(job) = self.pop_runnable() {
            return Some(job);
        }
        self.settle_quiescent_waits(sessions);
        self.pop_runnable()
    }
}

impl<T: RawSpanTelemetry> ExecutionContext<'_, T> {
    pub(crate) fn drive_for(&mut self, timeout: Option<Duration>) -> DriveOutcome<Job, DependencyKey> {
        let deadline = timeout.map(|limit| Instant::now() + limit);
        self.drive_until(deadline, timeout, true)
    }

    /// Applies only work already on the agenda (including exact wakes it
    /// causes). Root-product reconciliation uses this boundary to publish
    /// queued edits without expanding unrelated standing demand. It leaves
    /// quiescent questions indexed, not half-arbitrated: the requested
    /// product's exact fact wait settles and immediately publishes any
    /// readiness movement it needs. Fatal or timed-out execution still exits
    /// before the queue is drained, so the caller cannot assume edit
    /// visibility and must reject the request.
    pub(crate) fn drain_pending_for(&mut self, timeout: Option<Duration>) -> DriveOutcome<Job, DependencyKey> {
        let deadline = timeout.map(|limit| Instant::now() + limit);
        self.drive_until(deadline, timeout, false)
    }

    /// Runs queued jobs until the work graph has no ready work.
    ///
    /// Each job gets one telemetry span whose start owns job identity and whose
    /// payload-free stop records elapsed time. The separate
    /// `work_graph.applied` event that `complete_job` emits owns the raw
    /// `World` and `JobCompletion` causal payload. A fatal job records the
    /// span's exception lifecycle, closes the drive span as fatal, and stops
    /// the loop.
    #[cfg(test)]
    pub fn drive(&mut self) -> DriveOutcome<Job, DependencyKey> {
        if self.product_sessions.is_none() {
            let mut sessions = super::pull::ProductSessions::default();
            return ExecutionContext::with_product_sessions(self.world, self.telemetry, &mut sessions)
                .drive_until(None, None, true);
        }
        self.drive_until(None, None, true)
    }

    fn drive_until(
        &mut self,
        deadline: Option<Instant>,
        timeout: Option<Duration>,
        settle_quiescent_on_drain: bool,
    ) -> DriveOutcome<Job, DependencyKey> {
        let ExecutionContext {
            world,
            telemetry,
            product_sessions,
        } = self;
        let tel = *telemetry;
        world.clear_reported_warnings();
        let span = tel.raw_span0_1::<DriveOutcome<Job, DependencyKey>>(&["fz", "compiler2", "drive"]);
        let mut jobs_ran = 0_u64;
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
                    let Some(job) = world.pop_runnable() else {
                        break;
                    };
                    let job_span = start_job_span(tel, &job);
                    let result = super::jobs::run(
                        &mut ExecutionContext::with_optional_product_sessions(
                            world,
                            tel,
                            product_sessions.as_deref_mut(),
                        ),
                        &job,
                    );
                    match result {
                        Ok(effects) => {
                            jobs_ran += 1;
                            ExecutionContext::with_optional_product_sessions(
                                world,
                                tel,
                                product_sessions.as_deref_mut(),
                            )
                            .complete_job(job, effects);
                            stop_job_span(job_span);
                        }
                        Err(_) => {
                            job_span.exception();
                            world.clear_unresolved_diagnostics();
                            ExecutionContext::new(world, tel).flush_reported_warnings();
                            break 'outcome DriveOutcome::Fatal { job };
                        }
                    }
                }
                match ExecutionContext::with_optional_product_sessions(world, tel, product_sessions.as_deref_mut())
                    .drive_product_requests()
                {
                    Ok(true) => continue 'drive,
                    Ok(false) => {}
                    Err((address, _)) => {
                        break 'outcome DriveOutcome::DependencyFailed {
                            dependency: DependencyKey::Product(address),
                        };
                    }
                }
                if !settle_quiescent_on_drain {
                    world.clear_unresolved_diagnostics();
                    ExecutionContext::new(world, tel).flush_reported_warnings();
                    break 'outcome DriveOutcome::Resolved;
                }
                // The agenda drained. Every need starts its producer the
                // moment it is recorded (`World::demand_recorded_needs`,
                // `World::park_on_gates`), so there is no standing demand
                // left to discover here -- the only drain work left is
                // arbitration: every settled question standing over a
                // quiesced cone is answerable. Answering one can satisfy a
                // standing settled wait and wake real work, so a wake sends
                // the loop back around; silence ends the drive.
                world.settle_quiescent_waits(product_sessions.as_deref());
                let quiesced = flush_quiescence(world, tel);
                for step in &quiesced {
                    ExecutionContext::with_optional_product_sessions(world, tel, product_sessions.as_deref_mut())
                        .publish_dependency_movements(&step.movements);
                }
                if quiescence_woke_work(&quiesced) {
                    continue 'drive;
                }
                break 'drive;
            }
            if !world.work_graph.has_unresolved() {
                world.clear_unresolved_diagnostics();
                ExecutionContext::new(world, tel).flush_reported_warnings();
                DriveOutcome::Resolved
            } else {
                let waits = ExecutionContext::new(world, tel).report_unresolved_waits();
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
) -> Vec<super::AppliedStep<Job, DependencyKey>> {
    let steps = world.take_quiescence_steps();
    for step in &steps {
        tel.raw_event1(&["fz", "compiler2", "work_graph", "quiesced"], step);
    }
    steps
}

/// Whether any of `steps` started work.
pub(super) fn quiescence_woke_work(steps: &[super::AppliedStep<Job, DependencyKey>]) -> bool {
    steps.iter().any(|step| !step.wakes.is_empty())
}

fn emit_drive_timed_out(tel: &impl crate::telemetry::Telemetry, timeout: &Option<Duration>) {
    tel.raw_event1(&["fz", "compiler2", "drive", "timed_out"], timeout);
}

pub(super) fn start_job_span<'a, T: RawSpanTelemetry>(
    tel: &'a T,
    job: &Job,
) -> <T as RawSpanTelemetry>::Span1_0<'a, Job> {
    tel.raw_span1_0::<Job>(&["fz", "compiler2", "job"], job)
}

pub(super) fn stop_job_span(span: impl RawSpanStop0) {
    span.stop0();
}
