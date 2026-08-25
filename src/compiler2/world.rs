//! Compiler2's owned world state.
//!
//! Compiler-owned identities are total here. A `CodeId`, `ModuleId`,
//! `FunctionId`, or `RootId` that came from Compiler2 must resolve; a bad id is
//! a bug and should panic at the lookup boundary. `Option` is reserved for
//! legitimate state absence like "this known function is still a placeholder"
//! or "this known code has not been indexed yet".

use std::any::Any;
#[cfg(test)]
use std::cell::Cell;
use std::cmp::Reverse;
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::FunctionSurface;
use crate::diag::diagnostic::Severity;
use crate::diag::driver::emit_through;
use crate::diag::{Diagnostic, codes};
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardDispatch};
use crate::modules::identity::{Mfa, ModuleName};
use crate::modules::runtime_library;
use crate::source::Span;
use crate::telemetry::{Telemetry, TelemetryExt as _};

use super::CodeId;
use super::artifact::{
    BackendProgram, BackendProgramMap, MacroExecutable, MacroExecutableMap, NativeProgram, NativeProgramMap,
};
use super::body::{LoweredBody, LoweredBodyMap};
use super::code::{CodeMap, CodeState, QuotedCodeSource};
use super::contract::{FunctionContract, FunctionContractMap};
use super::deps::UnresolvedWait;
use super::dispatch::{EntryDispatchMap, GuardDispatchMap};
use super::drive::{ExecutionContext, FactKey, Job, JobEffects, WorkGraph};
#[cfg(test)]
use super::facts::FactUse;
use super::identity::{
    ActivationKey, ExecutableKey, ExecutableNeed, ExpandedFunctionSourceMap, FunctionId, FunctionMap, FunctionRef,
    FunctionSource, ModuleId, ModuleMap, ModuleSourceKind, ModuleState, NotedTypeDecl, PendingFunctionSourceMap,
    RootEntry, RootId, RootKind, RootMap, TypeDeclMap, TypeName, TypeRefMap,
};
use super::keying::{BodyKeying, BodyKeyingMap, DispatchDemand, DispatchMaskMap};
use super::module_interface::{
    InterfaceCallableKind, InterfaceExpectation, InterfaceRequester, ModuleInterface, ModuleReferenceExpectation,
    ModuleReferenceExpectationMap,
};
use super::namespace::{Namespace, NamespaceStore, NamespaceSymbol};
use super::ordered_set::OrderedSet;
use super::protocol::{
    ProtocolCallback, ProtocolCallbackImpl, ProtocolCallbackMap, ProtocolDispatch, ProtocolDispatchArm,
    ProtocolDispatchMap, ProtocolImpl, ProtocolImplKey, ProtocolImplMap, ProtocolImplProviderMap, protocol_domain_tag,
};
use super::quoted_surface::{ReservedSourceDefinition, ScopeForm, reserved_source_definition};
use super::runtime::{self, RuntimeModuleCode};
use super::scheduler::{FatalError, WorkStartReason, WorkStartTally};
use super::scope::ScopeSnapshot;
use super::semantic::{
    ActivationAnalysis, ActivationInputAlternatives, ActivationInputMap, ActivationMap, CallSiteKey, CallSiteMap,
    CallSiteSummary, CallSiteTargets, CallSiteTargetsMap, ContributionReplace,
};
use super::source::{
    QuotedLexicalContext, QuotedLexicalContextKind, QuotedSourceBuilder, QuotedSourceError, QuotedSourceMetadata,
    QuotedSourceRoot,
};
use super::structdef::{
    StructDef, StructDefMap, StructExpectationMap, StructFieldExpectation, StructReferenceExpectation,
};
use super::transport::{
    BoundaryDescr, BoundaryId, CallableDescr, CallableId, LaneDescr, LaneId, ShapeDescr, ShapeId, TransportStore,
};
use super::typedef::{TypeDef, TypeDefMap};
use super::types::{ClosureTarget, MapKey, Ty, Types};
use crate::ir_interp::AnyValue as RuntimeValue;
use fz_runtime::any_value::AnyValueRef;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum UnresolvedIssueKey {
    Module(ModuleId),
    Struct(ModuleId),
    Function(FunctionId),
    Export(FunctionId),
}

struct UnresolvedIssue {
    key: UnresolvedIssueKey,
    diagnostic: Diagnostic,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct WarningDiagnosticKey {
    code: &'static str,
    message: String,
    primary: Span,
}

impl WarningDiagnosticKey {
    fn from_diagnostic(diagnostic: &Diagnostic) -> Self {
        Self {
            code: diagnostic.code.0,
            message: diagnostic.message.clone(),
            primary: diagnostic.primary.span,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum CallableMatchScore {
    VariadicPrefix(usize),
    Exact,
}

pub struct World {
    code: CodeMap,
    modules: ModuleMap,
    functions: FunctionMap,
    pending_function_sources: PendingFunctionSourceMap,
    expanded_function_sources: ExpandedFunctionSourceMap,
    type_decls: TypeDeclMap,
    type_refs: TypeRefMap,
    type_defs: TypeDefMap,
    struct_defs: StructDefMap,
    struct_expectations: StructExpectationMap,
    module_reference_expectations: ModuleReferenceExpectationMap,
    function_contracts: FunctionContractMap,
    bodies: LoweredBodyMap,
    guard_dispatches: GuardDispatchMap,
    entry_dispatches: EntryDispatchMap,
    body_keying: BodyKeyingMap,
    dispatch_masks: DispatchMaskMap,
    protocol_callbacks: ProtocolCallbackMap,
    protocol_impls: ProtocolImplMap,
    protocol_dispatches: ProtocolDispatchMap,
    protocol_impl_providers: ProtocolImplProviderMap,
    activations: ActivationMap,
    activation_inputs: ActivationInputMap<Job>,
    callsites: CallSiteMap,
    callsite_targets: CallSiteTargetsMap,
    backend: BackendProgramMap,
    macro_executables: MacroExecutableMap,
    native: NativeProgramMap,
    roots: RootMap,
    macro_roots: HashMap<FunctionId, RootId>,
    namespaces: NamespaceStore,
    types: Types,
    transport: TransportStore,
    runtime_prelude: CodeId,
    /// Additional user-surface preludes scoped in over the runtime prelude, in
    /// registration order. Each is ordinary user source (read + expanded like
    /// any submission, unlike the bootstrap runtime prelude) whose scope
    /// advances `prelude_head`, so every later submission sees its bindings
    /// without any textual splicing into the user's own source buffer. The
    /// `fz2 test` front door registers exactly one — the `test` item macro —
    /// scoped into that run's world only, never the global Kernel bootstrap.
    extra_preludes: Vec<CodeId>,
    runtime_modules: HashMap<ModuleId, RuntimeModuleCode>,
    reported_unresolved: HashSet<UnresolvedIssueKey>,
    reported_warnings: HashSet<WarningDiagnosticKey>,
    warning_diagnostics: Vec<Diagnostic>,
    /// Discovered callee activations whose `ActivationAnalyzed` fact is not
    /// yet settled: the standing demand `drive::demand_activation_frontier_analyses`
    /// expands, the non-root analogue of the roots' own standing demand.
    /// `complete_job` is the sole maintenance site — it inserts a key when a
    /// job outputs `Activation(key)` (unless already settled) and removes it
    /// once `ActivationAnalyzed(key)` settles.
    activation_frontier: HashSet<ActivationKey>,
    pub(crate) work_graph: WorkGraph,
    #[cfg(test)]
    telemetry_query_count: Cell<u64>,
}

pub(crate) struct JobCompletion {
    pub(crate) job: Job,
    pub(crate) step: super::AppliedStep<Job, FactKey>,
    pub(crate) activation_input_changed: HashSet<ActivationKey>,
    pub(crate) rebased: bool,
}

impl std::ops::Deref for JobCompletion {
    type Target = super::AppliedStep<Job, FactKey>;

    fn deref(&self) -> &Self::Target {
        &self.step
    }
}

struct RuntimeModuleRegistration {
    code_id: CodeId,
    inserted: bool,
}

impl std::fmt::Debug for World {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("World")
            .field("code", &self.code)
            .field("modules", &self.modules)
            .field("functions", &self.functions)
            .field("function_contracts", &self.function_contracts)
            .field("bodies", &self.bodies)
            .field("roots", &self.roots)
            .field("namespaces", &self.namespaces)
            .field("transport", &self.transport)
            .field("runtime_prelude", &self.runtime_prelude)
            .field("runtime_modules", &self.runtime_modules)
            .field("work_graph", &self.work_graph)
            .finish()
    }
}

impl Default for World {
    fn default() -> Self {
        Self::new()
    }
}

impl World {
    #[cfg(test)]
    pub(crate) fn telemetry_query_count(&self) -> u64 {
        self.telemetry_query_count.get()
    }

    pub fn new() -> Self {
        let mut world = Self {
            code: CodeMap::new(),
            modules: ModuleMap::new(),
            functions: FunctionMap::new(),
            pending_function_sources: PendingFunctionSourceMap::new(),
            expanded_function_sources: ExpandedFunctionSourceMap::new(),
            type_decls: TypeDeclMap::new(),
            type_refs: TypeRefMap::new(),
            type_defs: TypeDefMap::new(),
            struct_defs: StructDefMap::new(),
            struct_expectations: StructExpectationMap::new(),
            module_reference_expectations: ModuleReferenceExpectationMap::new(),
            function_contracts: FunctionContractMap::new(),
            bodies: LoweredBodyMap::new(),
            guard_dispatches: GuardDispatchMap::new(),
            entry_dispatches: EntryDispatchMap::new(),
            body_keying: BodyKeyingMap::new(),
            dispatch_masks: DispatchMaskMap::new(),
            protocol_callbacks: ProtocolCallbackMap::new(),
            protocol_impls: ProtocolImplMap::new(),
            protocol_dispatches: ProtocolDispatchMap::new(),
            protocol_impl_providers: ProtocolImplProviderMap::new(),
            activations: ActivationMap::new(),
            activation_inputs: ActivationInputMap::new(),
            callsites: CallSiteMap::new(),
            callsite_targets: CallSiteTargetsMap::new(),
            backend: BackendProgramMap::new(),
            macro_executables: MacroExecutableMap::new(),
            native: NativeProgramMap::new(),
            roots: RootMap::new(),
            macro_roots: HashMap::new(),
            namespaces: NamespaceStore::new(),
            types: Types::new(),
            transport: TransportStore::new(),
            runtime_prelude: CodeId::ZERO,
            extra_preludes: Vec::new(),
            runtime_modules: HashMap::new(),
            reported_unresolved: HashSet::new(),
            reported_warnings: HashSet::new(),
            warning_diagnostics: Vec::new(),
            activation_frontier: HashSet::new(),
            work_graph: WorkGraph::new(),
            #[cfg(test)]
            telemetry_query_count: Cell::new(0),
        };
        world.runtime_modules = runtime::bootstrap(&mut world.modules);
        world.runtime_prelude = world.code.define(
            Some("runtime:runtime.fz".to_string()),
            runtime_library::prelude_source().to_string(),
        );
        world
    }

    pub fn root_function(&self, root: RootId) -> FunctionId {
        self.roots.get(root).function
    }

    pub(crate) fn types(&self) -> &Types {
        &self.types
    }

    pub(crate) fn telemetry_counts(&self) -> (usize, usize, usize) {
        (
            self.code.len(),
            self.roots.ids().count(),
            self.activation_frontier.len(),
        )
    }

    pub(crate) fn types_mut(&mut self) -> &mut Types {
        &mut self.types
    }

    /// The runtime boundary: hand the backend interpreter the types and the
    /// transport store together. This is the *only* place the whole store leaves
    /// World — every compiler-internal access goes through the interning gateway
    /// below, never the raw interners.
    pub(crate) fn types_mut_and_transport(&mut self) -> (&mut Types, &TransportStore) {
        (&mut self.types, &self.transport)
    }

    // ---- Transport interning gateway ------------------------------------
    //
    // World is the sole owner of the transport interners. A transport id
    // (`ShapeId`/`LaneId`/`CallableId`/`BoundaryId`) is only ever minted by an
    // `intern_*` method here, which *guarantees* the descriptor is interned, and
    // is only ever resolved by the matching lookup here. The interning mechanism
    // (`TransportStore::interners`) is never exposed, so no caller can fabricate
    // an id or reach a descriptor without going through this contract.

    pub fn intern_shape(&mut self, descr: ShapeDescr) -> ShapeId {
        self.transport.interners_mut().intern_shape(descr)
    }

    pub fn shape(&self, id: ShapeId) -> &ShapeDescr {
        self.transport.interners().shape(id)
    }

    pub fn shape_width(&self, shape: ShapeId) -> usize {
        self.transport.interners().shape_width(shape)
    }

    pub fn shape_lane_ids(&self, shape: ShapeId) -> Vec<LaneId> {
        self.transport.interners().shape_lane_ids(shape)
    }

    pub fn shape_leaf_lanes(&self, shape: ShapeId) -> Vec<(ShapeId, LaneId)> {
        self.transport.interners().shape_leaf_lanes(shape)
    }

    pub fn tuple_field_spans(&self, shape: ShapeId) -> Option<Vec<(ShapeId, std::ops::Range<usize>)>> {
        self.transport.interners().tuple_field_spans(shape)
    }

    pub fn shape_count(&self) -> usize {
        self.transport.interners().shape_count()
    }

    pub fn intern_lane(&mut self, descr: LaneDescr) -> LaneId {
        self.transport.interners_mut().intern_lane(descr)
    }

    pub fn lane(&self, id: LaneId) -> &LaneDescr {
        self.transport.interners().lane(id)
    }

    pub fn lane_count(&self) -> usize {
        self.transport.interners().lane_count()
    }

    pub fn intern_callable(&mut self, descr: CallableDescr) -> CallableId {
        self.transport.interners_mut().intern_callable(descr)
    }

    pub fn callable(&self, id: CallableId) -> &CallableDescr {
        self.transport.interners().callable(id)
    }

    pub fn callable_count(&self) -> usize {
        self.transport.interners().callable_count()
    }

    pub fn intern_boundary(&mut self, descr: BoundaryDescr) -> BoundaryId {
        self.transport.interners_mut().intern_boundary(descr)
    }

    pub fn boundary(&self, id: BoundaryId) -> &BoundaryDescr {
        self.transport.interners().boundary(id)
    }

    pub fn boundary_count(&self) -> usize {
        self.transport.interners().boundary_count()
    }

    pub fn shapes(&self) -> impl Iterator<Item = (ShapeId, &ShapeDescr)> + '_ {
        self.transport.interners().shapes()
    }

    pub fn lanes(&self) -> impl Iterator<Item = (LaneId, &LaneDescr)> + '_ {
        self.transport.interners().lanes()
    }

    pub fn callables(&self) -> impl Iterator<Item = (CallableId, &CallableDescr)> + '_ {
        self.transport.interners().callables()
    }

    pub fn boundaries(&self) -> impl Iterator<Item = (BoundaryId, &BoundaryDescr)> + '_ {
        self.transport.interners().boundaries()
    }

    /// Registers submitted source text under a fresh id and emits the
    /// `code.submitted` observation. This does NOT enqueue any indexing or
    /// scoping job: it only makes the code demandable, so a wait on
    /// `CodeIndexed(code_id)`/`CodeScoped(code_id)` reaches the minting job
    /// through the fact->producer pull (`demand_fact_producer`'s
    /// `CodeIndexed -> IndexCode`, `CodeScoped -> ScopeCode` arms). The eager
    /// enqueue that turns registration into a driven work-start is the caller's
    /// choice — `submit_code` (the external front door) drives it as
    /// `Ignition`; internal runtime-module minting (`ensure_runtime_module`)
    /// leaves it to be pulled.
    pub fn submit_module_interface(&mut self, module_name: String, interface: ModuleInterface) -> ModuleId {
        let module = self.reference_module(module_name);
        self.define_module_interface(module, interface);
        // External front door: the same ignition shape as `submit_code`/`submit_root`.
        self.work_graph
            .enqueue(Job::DefineModuleInterface(module), WorkStartReason::Ignition);
        module
    }

    pub(crate) fn complete_job(&mut self, job: Job, effects: JobEffects) -> JobCompletion {
        let reads = effects.reads.into_iter().collect();
        let waits: HashSet<_> = effects.waits.into_iter().collect();
        // Waiting completions extend: a blocked job's prior contributions
        // stand untouched (the scheduler likewise keeps its claims standing).
        // A wait-free conclusion normally replaces the contribution key set.
        // Activation-input evidence from semantic analysis is cumulative caller
        // evidence: a rerun can add/widen, but a temporarily unreachable callsite
        // cannot lower and re-raise the same body input edge. Non-semantic
        // publishers still use normal replacement so source/root changes can
        // withdraw genuinely stale external contributions.
        let rebased = self.work_graph.rebased(&job);
        // The work graph is the single source of truth for each publisher's
        // prior output frontier (it tracks every job's facts under the identical
        // accumulate-on-extend / replace-on-conclude rule). Both contribution
        // stores read their retraction frontier from it, filtered to their fact.
        let previous_output_keys = self.work_graph.output_keys(&job);
        let previous_activation_input_outputs = previous_output_keys
            .iter()
            .filter_map(|fact| match fact {
                FactKey::ActivationInputs(key) => Some(key.clone()),
                _ => None,
            })
            .collect::<HashSet<_>>();
        let ContributionReplace {
            output_keys: activation_input_outputs,
            changed_keys: activation_input_changed,
        } = if waits.is_empty() {
            self.conclude_activation_input_contributions(
                &job,
                previous_activation_input_outputs,
                effects.activation_input_contributions,
                rebased,
            )
        } else {
            self.extend_activation_input_contributions(&job, effects.activation_input_contributions)
        };
        let mut outputs = effects.outputs;
        outputs.extend(activation_input_outputs.into_iter().map(FactKey::ActivationInputs));
        let outputs = dedupe_job_facts(outputs);
        let mut changed = effects.changed;
        changed.extend(activation_input_changed.iter().cloned().map(FactKey::ActivationInputs));
        let changed = dedupe_job_facts(changed);
        // Captured before `outputs` moves into `complete`: the two record
        // sites keep `activation_frontier` in lockstep with the fact table.
        let activation_published: Vec<ActivationKey> = outputs
            .iter()
            .filter_map(|fact| match fact {
                FactKey::Activation(key) => Some(key.clone()),
                _ => None,
            })
            .collect();
        let analyzed_published: Vec<ActivationKey> = outputs
            .iter()
            .filter_map(|fact| match fact {
                FactKey::ActivationAnalyzed(key) => Some(key.clone()),
                _ => None,
            })
            .collect();
        let step = self.work_graph.complete(&job, reads, waits, outputs, changed);
        for key in analyzed_published {
            if self.fact_is_settled(&FactKey::ActivationAnalyzed(key.clone())) {
                self.activation_frontier.remove(&key);
            }
        }
        for key in activation_published {
            self.note_activation_frontier(key);
        }
        JobCompletion {
            job,
            step,
            activation_input_changed,
            rebased,
        }
    }

    /// The SOLE insertion point into `activation_frontier`: a discovered
    /// `Activation(key)` publish becomes a standing analysis demand unless
    /// its `ActivationAnalyzed` fact has already settled.
    fn note_activation_frontier(&mut self, key: ActivationKey) {
        if !self.fact_is_settled(&FactKey::ActivationAnalyzed(key.clone())) {
            self.activation_frontier.insert(key);
        }
    }

    /// The activations `drive::demand_activation_frontier_analyses` still
    /// owes a first-run demand. Order carries no meaning — demanding
    /// producers is commutative — so no sort applies.
    pub(crate) fn activation_frontier_keys(&self) -> Vec<ActivationKey> {
        self.activation_frontier.iter().cloned().collect()
    }

    /// Drops a key `demand_activation_frontier_analyses` has determined no
    /// longer needs first-run ignition (already analyzed at least once, or
    /// settled).
    pub(crate) fn retire_activation_frontier(&mut self, key: &ActivationKey) {
        self.activation_frontier.remove(key);
    }

    /// The manual, unattributed demand entry point: nothing here names a
    /// sanctioned reason, so this always tallies `Unclassified`. Production
    /// never calls this directly (the front door is `submit_code`/
    /// `submit_module_interface`/`submit_root`, and every internal expansion
    /// carries its own `WorkStartReason` through `work_graph.enqueue`
    /// directly) -- it exists for tests that seed jobs without going through
    /// submission.
    pub fn demand(&mut self, job: Job) -> bool {
        self.work_graph.enqueue(job, WorkStartReason::Unclassified)
    }

    /// The cumulative work-start attribution snapshot for this world: how many
    /// jobs entered the agenda under each `WorkStartReason`, plus the
    /// whole-fact-table-scan count. See `WorkStartReason` for the taxonomy.
    pub fn work_start_tally(&self) -> WorkStartTally {
        self.work_graph.work_start_tally()
    }

    pub(crate) fn clear_unresolved_diagnostics(&mut self) {
        self.reported_unresolved.clear();
    }

    pub(crate) fn clear_reported_warnings(&mut self) {
        self.reported_warnings.clear();
        self.warning_diagnostics.clear();
    }

    pub(crate) fn note_warning_once(&mut self, diagnostic: Diagnostic) {
        debug_assert_eq!(diagnostic.severity, Severity::Warning);
        if self
            .reported_warnings
            .insert(WarningDiagnosticKey::from_diagnostic(&diagnostic))
        {
            self.warning_diagnostics.push(diagnostic);
        }
    }

    pub fn code_name(&self, id: CodeId) -> Option<&str> {
        self.code.name(id)
    }

    pub fn code_text(&self, id: CodeId) -> &str {
        #[cfg(test)]
        self.telemetry_query_count.set(self.telemetry_query_count.get() + 1);
        self.code.text(id)
    }

    pub(crate) fn source_map(&self) -> std::rc::Rc<std::cell::RefCell<crate::source::SourceMap>> {
        self.code.source_map()
    }

    pub fn root_entry(&self, id: RootId) -> RootEntry {
        self.roots.get(id).clone()
    }

    pub(crate) fn root_ids(&self) -> impl Iterator<Item = RootId> + use<> {
        self.roots.ids()
    }

    pub(crate) fn activation_key(&mut self, root: RootId, function: FunctionId, inputs: &[Ty]) -> ActivationKey {
        self.canonical_activation_key(root, function, inputs)
    }

    /// The correlated body-input evidence of an activation, once its fact
    /// exists: the canonical antichain of publisher rows. Semantic analysis
    /// reads THIS — each row is analyzed independently, never a column mix.
    pub(crate) fn activation_input_alternatives(&self, key: &ActivationKey) -> Option<&ActivationInputAlternatives> {
        #[cfg(test)]
        self.telemetry_query_count.set(self.telemetry_query_count.get() + 1);
        self.fact_revision(&FactKey::ActivationInputs(key.clone()))?;
        self.activation_inputs.get(key)
    }

    /// The column-wise joined projection of the activation's input rows —
    /// correlation-blind by construction. Only for consumers whose question is
    /// genuinely per-column (transport lane typing), after semantic decisions.
    pub(crate) fn activation_inputs_joined(&self, key: &ActivationKey) -> Option<Vec<Ty>> {
        self.fact_revision(&FactKey::ActivationInputs(key.clone()))?;
        Some(self.activation_inputs.get(key)?.joined().to_vec())
    }

    pub fn activation_analysis(&self, key: &ActivationKey) -> Option<&ActivationAnalysis> {
        #[cfg(test)]
        self.telemetry_query_count.set(self.telemetry_query_count.get() + 1);
        self.activations.get(key).and_then(|slot| slot.analysis())
    }

    /// The activation's current return EVIDENCE. `None` means the claim is
    /// retracted or no path has produced a value yet — the ascent's bottom,
    /// never the type `none`. Behind the settled gate, a still-`None` read
    /// is the fixpoint fact "provably never returns" (Kleene), and only
    /// there may consumers convert it to the empty type.
    pub fn activation_return(&self, key: &ActivationKey) -> Option<Ty> {
        self.fact_revision(&FactKey::ReturnType(key.clone()))?;
        self.activations.get(key).and_then(|slot| slot.return_ty().cloned())
    }

    pub(crate) fn activation_return_evidence(&self, key: &ActivationKey) -> Option<Ty> {
        #[cfg(test)]
        self.telemetry_query_count.set(self.telemetry_query_count.get() + 1);
        self.activations.get(key).and_then(|slot| slot.return_ty().copied())
    }

    fn conclude_activation_input_contributions(
        &mut self,
        job: &Job,
        previous_output_keys: HashSet<ActivationKey>,
        contributions: Vec<(ActivationKey, Vec<Ty>)>,
        rebased: bool,
    ) -> ContributionReplace<ActivationKey> {
        let next = self.normalize_contributions(contributions);
        let preserve_frontier = rebased || matches!(job, Job::AnalyzeActivation(_));
        if preserve_frontier {
            self.activation_inputs.conclude_preserving_frontier(
                &mut self.types,
                job.clone(),
                previous_output_keys,
                next,
            )
        } else {
            self.activation_inputs
                .conclude(&mut self.types, job.clone(), previous_output_keys, next, false)
        }
    }

    fn extend_activation_input_contributions(
        &mut self,
        job: &Job,
        contributions: Vec<(ActivationKey, Vec<Ty>)>,
    ) -> ContributionReplace<ActivationKey> {
        let next = self.normalize_contributions(contributions);
        self.activation_inputs.extend(&mut self.types, job.clone(), next)
    }

    fn normalize_contributions(
        &mut self,
        contributions: Vec<(ActivationKey, Vec<Ty>)>,
    ) -> HashMap<ActivationKey, ActivationInputAlternatives> {
        let mut next = HashMap::<ActivationKey, ActivationInputAlternatives>::new();
        for (activation, inputs) in contributions {
            // Canonicalize the input evidence the same whole-scope way the key is
            // built (fz-hwn.27.6, A): one shared addressing pass, so distinct
            // observed vars stay distinct and the evidence shares the key's
            // canonical form. Idempotent on already-addressed contributions.
            let normalized = self.types.address_inputs(&inputs);
            let normalized = if self
                .body_keying
                .get(activation.function)
                .is_some_and(|keying| keying.recursive)
            {
                let mask = self
                    .dispatch_masks
                    .get(activation.function)
                    .cloned()
                    .unwrap_or_else(|| vec![DispatchDemand::Whole; normalized.len()]);
                self.types.convergence_collapse_evidence_inputs(&normalized, &mask)
            } else {
                normalized
            };
            // Each contribution stays one correlated row (fz-9i4.7.10.2):
            // a publisher's second row for the same activation is an
            // ALTERNATIVE, never a column-wise blend of the two.
            match next.entry(activation) {
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(ActivationInputAlternatives::from_row(normalized));
                }
                std::collections::hash_map::Entry::Occupied(mut entry) => {
                    entry.get_mut().push_row(&mut self.types, normalized);
                }
            }
        }
        next
    }

    pub fn callsite_summary(&self, key: &CallSiteKey) -> Option<&CallSiteSummary> {
        #[cfg(test)]
        self.telemetry_query_count.set(self.telemetry_query_count.get() + 1);
        self.callsites.get(key)
    }

    pub fn define_callsite_targets(&mut self, key: CallSiteKey, targets: CallSiteTargets) -> bool {
        self.callsite_targets.define(key, targets)
    }

    pub fn callsite_targets(&self, key: &CallSiteKey) -> Option<&CallSiteTargets> {
        self.callsite_targets.get(key)
    }

    pub(crate) fn backend_program(&self, root: RootId) -> BackendProgram {
        #[cfg(test)]
        self.telemetry_query_count.set(self.telemetry_query_count.get() + 1);
        self.backend
            .get(root)
            .cloned()
            .expect("backend programs should only be read after their fact is defined")
    }

    pub(crate) fn macro_root(&mut self, function: FunctionId) -> RootId {
        if let Some(root) = self.macro_roots.get(&function).copied() {
            return root;
        }
        let (source, surface) = self.function_definition(function);
        let any = self.types.any();
        let input = vec![any; 1 + source.capture_params.len() + surface.arity()];
        let root = self.roots.define(RootEntry {
            function,
            input,
            need: ExecutableNeed::Value,
            kind: RootKind::Macro,
        });
        self.macro_roots.insert(function, root);
        root
    }

    pub(crate) fn macro_executable(&self, function: FunctionId) -> Option<&MacroExecutable> {
        self.macro_executables.get(function)
    }

    pub(crate) fn native_program(&self, root: RootId) -> NativeProgram {
        self.native
            .get(root)
            .cloned()
            .expect("native programs should only be read after their fact is defined")
    }

    pub fn reference_module(&mut self, name: impl Into<String>) -> ModuleId {
        self.modules.reference_named(name)
    }

    #[cfg(test)]
    pub(crate) fn module_state(&self, module: ModuleId) -> ModuleState {
        self.modules.get(module).clone()
    }

    pub fn reference_child_module(&mut self, parent: ModuleId, local_name: &str) -> ModuleId {
        let name = self.qualified_module_name(parent, local_name);
        self.modules.reference_named(name)
    }

    pub fn define_module_interface(&mut self, id: ModuleId, interface: ModuleInterface) -> bool {
        self.modules.define_interface(id, interface)
    }

    pub(crate) fn merge_module_interface_expectations(
        &self,
        id: ModuleId,
        mut interface: ModuleInterface,
    ) -> ModuleInterface {
        if let Some(prior) = self.module_interface_if_present(id) {
            interface.inherit_expectations_from(&prior);
        }
        interface
    }

    pub fn index_module_body(
        &mut self,
        id: ModuleId,
        code: CodeId,
        parent: ModuleId,
        local_name: String,
        source: QuotedSourceRoot,
        surface: super::quoted_surface::ScopeSurface,
    ) -> bool {
        self.modules.index_body(id, code, parent, local_name, source, surface)
    }

    pub fn index_protocol_module(
        &mut self,
        id: ModuleId,
        code: CodeId,
        parent: ModuleId,
        local_name: String,
        source: QuotedSourceRoot,
        surface: super::quoted_surface::ScopeSurface,
    ) -> bool {
        self.modules
            .index_protocol(id, code, parent, local_name, source, surface)
    }

    pub fn index_protocol_impl_module(
        &mut self,
        id: ModuleId,
        code: CodeId,
        parent: ModuleId,
        local_name: String,
        source: QuotedSourceRoot,
        impl_source: super::identity::ProtocolImplSource,
    ) -> bool {
        self.modules
            .index_protocol_impl(id, code, parent, local_name, source, impl_source)
    }

    pub fn scope_module(&mut self, id: ModuleId, base_namespace: Namespace) {
        self.modules.scope(id, base_namespace);
    }

    pub fn reference_function(&mut self, module: ModuleId, name: impl Into<String>, arity: usize) -> FunctionId {
        self.functions.reference(module, name, arity)
    }

    /// Holds a `@type` declaration's unresolved decl — parsed body plus the
    /// namespace captured at its scope — under its identity, for
    /// `DeriveTypeDef` to read. No resolution, no type-algebra. The event is
    /// the surface-tier signal that a type name became a referenceable identity.
    pub fn type_decl(&self, name: &TypeName) -> Option<&NotedTypeDecl> {
        #[cfg(test)]
        self.telemetry_query_count.set(self.telemetry_query_count.get() + 1);
        self.type_decls.get(name)
    }

    /// Resolves a type-position name against a captured scope to its identity,
    /// or `None` when it is not a named type (a builtin scalar, a free type
    /// variable, or an unresolvable bare name — all of which resolution, not
    /// the reference walk, decides). A dotted path resolves its module prefix
    /// and mints the provider module the way an import does; a bare name finds
    /// a `Type` binding in scope. Arity comes from the use site, so `t` and
    /// `t(a)` reference distinct identities.
    pub(crate) fn reference_type(&mut self, scope: Namespace, path: &[String], arity: usize) -> Option<TypeName> {
        match path {
            [] => None,
            [name] => self.lookup_type_name(scope, name).map(|bound| TypeName {
                module: bound.module,
                name: name.clone(),
                arity,
            }),
            [prefix @ .., leaf] => {
                let module = self.lookup_module_path(scope, &prefix.join("."))?;
                Some(TypeName {
                    module,
                    name: leaf.clone(),
                    arity,
                })
            }
        }
    }

    fn lookup_type_name(&self, head: Namespace, name: &str) -> Option<TypeName> {
        match self
            .namespaces
            .lookup_matching(head, name, |symbol| matches!(symbol, NamespaceSymbol::Type(_)))
        {
            Some(NamespaceSymbol::Type(type_name)) => Some(type_name.clone()),
            _ => None,
        }
    }

    /// Records the type names a function's contract surface references — its
    /// later `TypeDefined` wait-set (fz-rh2.12.4).
    // Consumed by the contract re-seat (fz-rh2.12.4); recorded one inch ahead.
    pub(crate) fn function_type_refs(&self, function: FunctionId) -> &[TypeName] {
        #[cfg(test)]
        self.telemetry_query_count.set(self.telemetry_query_count.get() + 1);
        self.type_refs.function_refs(function)
    }

    /// Records the type names a `@type` body references — the wait-set
    /// `DeriveTypeDef` resolves against before minting the symbol (fz-rh2.12.2).
    /// The type names a `@type` body references — `DeriveTypeDef`'s wait-set.
    pub(crate) fn type_def_refs(&self, name: &TypeName) -> &[TypeName] {
        #[cfg(test)]
        self.telemetry_query_count.set(self.telemetry_query_count.get() + 1);
        self.type_refs.type_refs(name)
    }

    /// Records the struct modules a `@type` body's `%Mod{...}` records name
    /// — the `StructDefined` half of `DeriveTypeDef`'s wait-set, alongside
    /// `record_type_def_refs`'s `TypeDefined` half (fz-rh2.17.5.6.10).
    pub(crate) fn record_type_def_struct_refs(&mut self, name: TypeName, mut refs: Vec<ModuleId>) {
        dedup_module_ids(&mut refs);
        self.type_refs.record_type_structs(name, refs);
    }

    /// The struct modules a `@type` body references — `DeriveTypeDef`'s
    /// `StructDefined` wait-set.
    pub(crate) fn type_def_struct_refs(&self, name: &TypeName) -> &[ModuleId] {
        self.type_refs.type_struct_refs(name)
    }

    /// Records the struct modules a function's type positions (`@spec`, param
    /// annotations, extern contract) reference — the `StructDefined` wait-set
    /// the contract and entry-dispatch jobs resolve against, the function
    /// mirror of `record_type_def_struct_refs`.
    pub(crate) fn record_function_type_struct_refs(&mut self, function: FunctionId, mut refs: Vec<ModuleId>) {
        dedup_module_ids(&mut refs);
        self.type_refs.record_function_structs(function, refs);
    }

    /// The struct modules a function's type positions reference — the
    /// contract/entry-dispatch `StructDefined` wait-set.
    pub(crate) fn function_type_struct_refs(&self, function: FunctionId) -> &[ModuleId] {
        self.type_refs.function_struct_refs(function)
    }

    /// Publishes a resolved type definition under `name` and emits the
    /// callee-tier `type defined` signal. The definition and the interner ride
    /// the event as opaque refs, so handlers that want the resolved surface
    /// render it themselves at event time.
    pub(crate) fn type_def(&self, name: &TypeName) -> Option<&TypeDef> {
        self.type_defs.get(name)
    }

    /// Reads `module`'s resolved `defstruct`, if `StructDefined(module)` has
    /// published one. There is no scan to fall back to: the protocol-impl-target
    /// classification and `struct_assertion_ty` read schemas through here.
    pub(crate) fn struct_def(&self, module: ModuleId) -> Option<&StructDef> {
        self.struct_defs.get(module)
    }

    /// Publishes a resolved `defstruct` under `module` and emits the
    /// callee-tier `struct_def defined` signal, mirroring `define_type_def`.
    /// This store is the single source of truth for struct schemas:
    /// `resolve.rs`'s `TypeExpr::StructRecord` path (via `struct_def_fields`),
    /// struct-literal/pattern lowering, protocol-impl-target classification,
    /// `struct_assertion_ty`, and the backend's whole-program schema
    /// inventory (`struct_def_schemas`) all read it.
    /// The precise, durable reader over `defstruct`'s ordered fields:
    /// `resolve.rs`'s `TypeExpr::StructRecord` classification reads this once
    /// it needs the schema. This never has an opinion when the fact has not
    /// published yet — callers that need the answer wait on
    /// `FactKey::StructDefined(module)` first (see `jobs::types::derive_type_def`).
    pub(crate) fn struct_def_fields(&self, module: ModuleId) -> Option<&[String]> {
        self.struct_defs.get(module).map(|def| def.fields.as_slice())
    }

    /// Records that `module` was used as a struct from `requester`, even when
    /// the reference named no fields. `unresolved_struct_issue` uses this
    /// module-level obligation to report a non-struct module at the reference
    /// site rather than falling back to a generated span.
    pub(crate) fn note_struct_reference_expectation(&mut self, module: ModuleId, requester: InterfaceRequester) {
        self.struct_expectations
            .record_reference(module, StructReferenceExpectation { requester });
    }

    /// Records that `field` was referenced on `module`'s struct from
    /// `requester`, mirroring `note_module_interface_expectation`. `A`'s
    /// `defstruct` has no dedicated re-derivation job to rewake the way
    /// `ModuleInterface` does when a late expectation lands, so this method
    /// is half of validate-on-settle: reference-then-settle is validated in
    /// `validate_struct_field_expectations` when `A` finally publishes;
    /// settle-then-reference (`A` already published) is checked right here,
    /// immediately, since nothing else would ever re-check it otherwise.
    /// Checks every outstanding field obligation on `module` against its
    /// published `defstruct` schema, mirroring
    /// `validate_module_interface_expectations`: a field named on a struct
    /// that does not declare it is diagnosed at the *requester's* span,
    /// independent of whether the struct or the reference settled first. A
    /// no-op until `module`'s `defstruct` has actually published. Every bad
    /// obligation is reported in one pass (two requesters each naming a bad
    /// field both surface), then the job is failed once.
    /// The struct module's declared value type, from its conventional `@type t`
    /// (arity 0). A struct's field types live in this declaration — `defstruct`
    /// carries only field names — so destructure/assertion must read it here
    /// rather than defaulting every field to `any` (fz-f98.8: an integer `Range`
    /// whose fields graduate to `any` makes `current + step` an `any + any` that
    /// the `+` overload widens to `int | float`).
    pub(crate) fn declared_struct_value_ty(&mut self, module: ModuleId) -> Option<Ty> {
        let name = TypeName {
            module,
            name: "t".to_string(),
            arity: 0,
        };
        let def = self.type_defs.get(&name)?.clone();
        Some(def.instantiate(&mut self.types, &[]))
    }

    pub(crate) fn protocol_dispatch(&self, protocol: ModuleId) -> Option<&ProtocolDispatch> {
        self.protocol_dispatches.get(protocol)
    }

    /// Records, from already-resolved ids, that `provider` declares the
    /// `(protocol, target)` impl. Resolution of the `defimpl`'s names happens at
    /// scope time where the namespace is available; this stores only ids.
    pub(crate) fn register_protocol_impl_provider(
        &mut self,
        protocol: ModuleId,
        target: ModuleId,
        provider: ModuleId,
    ) -> bool {
        self.protocol_impl_providers
            .register(ProtocolImplKey { protocol, target }, provider)
    }

    /// Every `(target, provider)` impl recorded for a protocol. The semantic
    /// tier reads this to demand a provider's definition for a matching
    /// receiver.
    pub(crate) fn protocol_impl_providers(&self, protocol: ModuleId) -> Vec<(ModuleId, ModuleId)> {
        self.protocol_impl_providers.providers_for_protocol(protocol)
    }

    pub(crate) fn is_protocol_domain_type(&self, name: &TypeName) -> bool {
        name.name == "t"
            && matches!(name.arity, 0 | 1)
            && matches!(
                self.modules.get(name.module),
                ModuleState::Indexed { source, .. }
                    | ModuleState::Scoped { source, .. }
                    | ModuleState::Defined { source, .. }
                    if matches!(source.kind, ModuleSourceKind::Protocol(_))
            )
    }

    /// The qualified tag a nominal `@type` (`refines` / `opaque`) brands under.
    /// A top-level type owns no module, so its tag is its bare name; a module
    /// type is tagged `Module.Path::name`.
    pub(crate) fn qualified_type_tag(&self, name: &TypeName) -> String {
        if self.is_protocol_domain_type(name)
            && let Some(protocol) = self.module_name(name.module)
        {
            return protocol_domain_tag(protocol);
        }
        if name.module.is_global() {
            return name.name.clone();
        }
        match self.module_name(name.module) {
            Some(path) if !path.is_empty() => format!("{}::{}", path, name.name),
            _ => name.name.clone(),
        }
    }

    /// Stashes the source form a scope walk built for `function` without minting
    /// the consumable `FunctionSource` fact (fz-f98.14.5). This is the eager
    /// interface-tier record: it carries everything a reference needs that lives
    /// outside the namespace (notably the variadic flag), while the body stays
    /// cold until a reached consumer pulls it through `PublishFunctionSource`. A
    /// function the program never reaches keeps its body cold here forever,
    /// exactly like an unreferenced `@type` decl.
    ///
    /// Returns whether the stashed content changed. The caller — the scope
    /// job's own conclusion — folds this into its `FactKey::FunctionSourceStash
    /// (function)` output/changed pair (fz-go4.38): a (re)scope is the only
    /// event that can supersede a body a consumer already pulled, and it must
    /// flow to `PublishFunctionSource` the same way every other re-derivation
    /// does, through a tracked fact's revision moving and waking the standing
    /// reader that named it — never a job enqueuing another job by name.
    pub(crate) fn pending_function_source(&self, function: FunctionId) -> Option<&FunctionSource> {
        self.pending_function_sources.get(function)
    }

    /// Promotes a stashed source into the consumable `FunctionSource` fact when a
    /// reached consumer demands the body. Returns `true` when the fact's content
    /// changed, so the caller publishes the change to the scheduler.
    pub(crate) fn function_source(&self, function: FunctionId) -> Option<FunctionSource> {
        match self.functions.get(function) {
            super::identity::FunctionState::Noted { source }
            | super::identity::FunctionState::Defined { source, .. } => Some(*source.clone()),
            super::identity::FunctionState::Placeholder => None,
        }
    }

    pub(crate) fn expanded_function_source(&self, function: FunctionId) -> Option<FunctionSource> {
        self.expanded_function_sources.get(function).cloned()
    }

    pub(crate) fn function_contract(&self, function: FunctionId) -> Option<&FunctionContract> {
        self.function_contracts.get(function)
    }

    pub(crate) fn function_declares_contract(&self, function: FunctionId) -> bool {
        match self.functions.get(function) {
            super::identity::FunctionState::Defined { surface, .. } => {
                surface.extern_abi.is_some()
                    || surface
                        .attrs
                        .iter()
                        .any(|attr| matches!(attr, crate::ast::Attribute::Spec(_)))
            }
            super::identity::FunctionState::Placeholder | super::identity::FunctionState::Noted { .. } => false,
        }
    }

    pub(crate) fn protocol_callback(&self, function: FunctionId) -> Option<ProtocolCallback> {
        self.protocol_callbacks.get(function)
    }

    pub(crate) fn protocol_impls_for(&self, protocol: ModuleId) -> Vec<(ProtocolImplKey, ProtocolImpl)> {
        let mut impls: Vec<_> = self
            .protocol_impls
            .impls_for_protocol(protocol)
            .map(|(key, protocol_impl)| (*key, protocol_impl.clone()))
            .collect();
        // `protocol_impls` is a hash map keyed by `(protocol, target)`; its
        // iteration order is a per-process `RandomState` artifact. This feeds
        // `ProtocolDispatch.arms`, a published fact compared by `PartialEq`
        // (order-sensitive `Vec` equality) to decide whether the fact
        // changed. An unsorted rebuild can reorder the same arm set between
        // revisions and look "changed" when nothing moved, and downstream
        // dispatch-arm consumers (protocol callsite resolution) would pick a
        // different first match run to run. Sorting by the target module —
        // unique per arm within one protocol — pins arm order to a stable,
        // demand-derived key instead of iteration order.
        impls.sort_by_key(|(key, _)| key.target.as_u32());
        impls
    }

    /// The one body-shape keying fact behind `FactKey::Recursive`: both
    /// answers (recursion, callable-identity consumption) publish as one
    /// value, so keying can never observe one without the other.
    pub(crate) fn define_body_keying(&mut self, function: FunctionId, keying: BodyKeying) -> bool {
        self.body_keying.define(function, keying)
    }

    pub(crate) fn define_dispatch_mask(&mut self, function: FunctionId, mask: Vec<DispatchDemand>) -> bool {
        self.dispatch_masks.define(function, mask)
    }

    pub(crate) fn entry_dispatch(&self, function: FunctionId) -> PatternDispatchPlan<Ty> {
        self.entry_dispatches
            .get(function)
            .cloned()
            .expect("entry dispatch should only be read after its fact is defined")
    }

    pub(crate) fn lowered_body(&self, function: FunctionId) -> LoweredBody {
        match self
            .bodies
            .get(function)
            .expect("body slots should exist before reading lowered bodies")
        {
            super::body::BodyState::Lowered(body) => body.clone(),
            super::body::BodyState::Placeholder => {
                panic!("lowered bodies should only be read after their fact is defined")
            }
        }
    }

    pub fn prelude_head(&self) -> Namespace {
        self.namespaces.prelude_head()
    }

    #[cfg(test)]
    pub(crate) fn runtime_prelude(&self) -> CodeId {
        self.runtime_prelude
    }

    /// Registers `text` as an additional user-surface prelude: ordinary source
    /// that is scoped in over the runtime prelude (and any earlier extra
    /// prelude) so its top-level definitions advance `prelude_head` and become
    /// visible to every later submission — without splicing text into any
    /// user source buffer, so every span keeps its true on-disk offset. The
    /// code is defined but not enqueued; it is pulled lazily when a later
    /// submission's scope waits on its `CodeScoped` fact, exactly as the
    /// runtime prelude is.
    pub(crate) fn register_scoped_prelude(&mut self, name: Option<String>, text: String) -> CodeId {
        let code_id = self.code.define(name, text);
        self.extra_preludes.push(code_id);
        code_id
    }

    /// The preludes whose scope must be settled before `code`'s own scope can
    /// base off `prelude_head`, in the order their bindings layer: the runtime
    /// prelude first, then each extra prelude registered before `code` itself.
    /// `code`'s own entry (if it is an extra prelude) is excluded so a prelude
    /// never waits on itself.
    pub(crate) fn preludes_to_await(&self, code: CodeId) -> Vec<CodeId> {
        if self.is_runtime_prelude(code) {
            return Vec::new();
        }
        let mut preludes = vec![self.runtime_prelude];
        for &extra in &self.extra_preludes {
            if extra == code {
                break;
            }
            preludes.push(extra);
        }
        preludes
    }

    /// True for any code whose scope advances `prelude_head`: the runtime
    /// prelude or a registered extra prelude.
    pub(crate) fn is_prelude(&self, code: CodeId) -> bool {
        self.is_runtime_prelude(code) || self.extra_preludes.contains(&code)
    }

    /// True only for *the* prelude source — the bootstrap code whose scope seeds
    /// `prelude_head`, the base namespace every other submission is scoped
    /// against. This is the namespace-base role, narrower than [`World::is_bootstrap`]:
    /// origin (is this bootstrap code) is not the same question as role (is this
    /// the namespace base).
    pub(crate) fn is_runtime_prelude(&self, code: CodeId) -> bool {
        code == self.runtime_prelude
    }

    /// True for compiler-owned bootstrap code: the prelude and the runtime
    /// library modules (Kernel, Enum, ...). Bootstrap code is parsed as canonical
    /// source — def-heads are definitions, not macro calls — because the macros
    /// that implement def-heads are themselves defined here. Every other
    /// submission is user surface. This is the one origin boundary that deserves
    /// special treatment.
    pub(crate) fn is_bootstrap(&self, code: CodeId) -> bool {
        self.is_runtime_prelude(code) || self.runtime_modules.values().any(|module| module.code_id == Some(code))
    }

    pub(crate) fn is_runtime_module(&self, module: ModuleId) -> bool {
        self.runtime_modules.contains_key(&module)
    }

    pub(crate) fn set_prelude_head(&mut self, head: Namespace) {
        self.namespaces.set_prelude_head(head);
    }

    pub fn bind_namespace(&mut self, head: Namespace, name: impl Into<String>, symbol: NamespaceSymbol) -> Namespace {
        self.namespaces.bind(head, name, symbol)
    }

    pub(crate) fn lookup_namespace(&self, head: Namespace, name: &str) -> Option<NamespaceSymbol> {
        self.namespaces.lookup(head, name).cloned()
    }

    pub fn module_interface(&self, module: ModuleId) -> ModuleInterface {
        self.modules
            .get(module)
            .interface()
            .cloned()
            .expect("module interface should only be read when it exists")
    }

    pub fn module_interface_if_present(&self, module: ModuleId) -> Option<ModuleInterface> {
        self.modules.get(module).interface().cloned()
    }

    pub(crate) fn module_has_source_state(&self, module: ModuleId) -> bool {
        self.modules.get(module).source().is_some()
    }

    pub fn note_module_interface_expectation(&mut self, module: ModuleId, expectation: InterfaceExpectation) {
        let mut interface = self.module_interface_if_present(module).unwrap_or_default();
        interface.record_expectation(expectation);
        self.define_module_interface(module, interface);
    }

    /// Records that `module` was referenced from `requester` without naming
    /// any one export -- a whole-module `import`/`require`, which has no
    /// `(name, arity)` to hang an [`InterfaceExpectation`] on. Mirrors
    /// `note_struct_reference_expectation`'s shape one for one: both note "a
    /// reference happened here" before the referenced thing is known to
    /// resolve, so `unresolved_module_issue` can name the real site instead
    /// of `Span::DUMMY` when the module never settles. Recorded into its own
    /// `module_reference_expectations` store, never into `ModuleInterface`
    /// itself -- `module_interface_if_present` doubles as "is this module's
    /// interface actually known," so stashing an obligation there would make
    /// an undefined module look resolved the moment someone referenced it.
    pub(crate) fn note_module_reference_expectation(&mut self, module: ModuleId, requester: InterfaceRequester) {
        self.module_reference_expectations
            .record(module, ModuleReferenceExpectation { requester });
    }

    pub fn reference_module_interface_callable(
        &mut self,
        module: ModuleId,
        name: String,
        arity: usize,
        kind: InterfaceCallableKind,
        requester: Option<InterfaceRequester>,
    ) -> FunctionId {
        let function = self.reference_function(module, name.clone(), arity);
        self.note_module_interface_expectation(
            module,
            InterfaceExpectation {
                name,
                arity,
                kind,
                requester,
            },
        );
        function
    }

    pub(crate) fn module_name(&self, module: ModuleId) -> Option<&str> {
        self.modules.name(module)
    }

    /// Every `defstruct` published so far, named by module, for the
    /// backend's whole-program schema inventory (`Prim::MakeStruct`'s schema
    /// registration and the interpreter's `AssertStruct`/`is_named_struct`
    /// checks both need every struct that might be constructed or matched
    /// against, not just the ones a single executable happens to construct
    /// literally). Fact-backed: this reads `StructDefMap` directly, replacing
    /// the old `ModuleStore::named_struct_schemas` source scan — a struct
    /// declared through a macro-emitted `defstruct` now appears here exactly
    /// like a source-written one.
    pub(crate) fn struct_def_schemas(&self) -> BTreeMap<String, Vec<String>> {
        self.struct_defs
            .iter()
            .filter_map(|(module, def)| {
                self.module_name(module)
                    .map(|name| (name.to_string(), def.fields.clone()))
            })
            .collect()
    }

    pub fn finish_code_index(&mut self, id: CodeId, source: QuotedCodeSource) -> bool {
        self.code.index(id, source)
    }

    pub fn finish_code_scope(&mut self, id: CodeId, namespace: Namespace) -> bool {
        self.code.scope(id, namespace)
    }

    pub fn module_defined_revision(&self, module: ModuleId) -> Option<u64> {
        if !matches!(self.modules.get(module), ModuleState::Defined { .. }) {
            return None;
        }
        self.work_graph.facts().revision(&FactKey::ModuleDefined(module))
    }

    pub fn module_interface_revision(&self, module: ModuleId) -> Option<u64> {
        self.work_graph.facts().revision(&FactKey::ModuleInterface(module))
    }

    pub fn function_defined_revision(&self, function: FunctionId) -> Option<u64> {
        if !matches!(
            self.functions.get(function),
            super::identity::FunctionState::Defined { .. }
        ) {
            return None;
        }
        self.work_graph.facts().revision(&FactKey::FunctionDefined(function))
    }

    pub(crate) fn function_contract_revision(&self, function: FunctionId) -> Option<u64> {
        self.work_graph.facts().revision(&FactKey::FunctionContract(function))
    }

    pub(crate) fn function_definition(&self, function: FunctionId) -> (FunctionSource, FunctionSurface) {
        match self.functions.get(function) {
            super::identity::FunctionState::Defined { source, surface, .. } => (*source.clone(), *surface.clone()),
            super::identity::FunctionState::Placeholder | super::identity::FunctionState::Noted { .. } => {
                panic!("function definitions should only be read from defined functions")
            }
        }
    }

    pub(crate) fn function_surface(&self, function: FunctionId) -> FunctionSurface {
        let (_, surface) = self.function_definition(function);
        surface
    }

    pub(crate) fn function_module(&self, function: FunctionId) -> ModuleId {
        self.functions.reference_for(function).module
    }

    pub(crate) fn function_ref(&self, function: FunctionId) -> &super::identity::FunctionRef {
        #[cfg(test)]
        self.telemetry_query_count.set(self.telemetry_query_count.get() + 1);
        self.functions.reference_for(function)
    }

    /// The reverse reference for `function`, or `None` when it is not a known
    /// function slot. Lets a caller probe an id of uncertain provenance (e.g. a
    /// decoded closure-surface var id) without panicking on an out-of-range id.
    #[cfg(test)]
    pub(crate) fn try_function_ref(&self, function: FunctionId) -> Option<&super::identity::FunctionRef> {
        self.functions.try_reference_for(function)
    }

    pub(crate) fn function_is_provider_boundary(&self, function: FunctionId) -> bool {
        let function_ref = self.function_ref(function);
        if function_ref.module.is_global()
            || self.module_defined_revision(function_ref.module).is_some()
            || self.module_has_source_state(function_ref.module)
            || self.is_runtime_module(function_ref.module)
            || self.function_defined_revision(function).is_some()
            || self.module_interface_revision(function_ref.module).is_none()
        {
            return false;
        }
        self.module_interface(function_ref.module)
            .callables()
            .iter()
            .any(|callable| callable.function == function)
    }

    pub(crate) fn function_mfa(&self, function: FunctionId) -> Mfa {
        let function_ref = self.function_ref(function);
        let module_name = self
            .module_name(function_ref.module)
            .expect("provider-boundary functions should belong to a named module");
        Mfa::new(
            ModuleName::parse_dotted(module_name).expect("compiler2 module names should be valid module paths"),
            function_ref.name.clone(),
            function_ref.arity,
        )
    }

    #[cfg(test)]
    pub(crate) fn function_scope(&self, function: FunctionId) -> Option<ScopeSnapshot> {
        let source = match self.functions.get(function) {
            super::identity::FunctionState::Defined { source, .. }
            | super::identity::FunctionState::Noted { source } => source.as_ref(),
            // Before the body is pulled the stash still records the owner scope.
            super::identity::FunctionState::Placeholder => self.pending_function_source(function)?,
        };
        Some(ScopeSnapshot::function(source.owner_module, source.namespace, function))
    }

    pub(crate) fn function_arity(&self, function: FunctionId) -> usize {
        self.functions.reference_for(function).arity
    }

    pub(crate) fn function_variadic(&self, function: FunctionId) -> bool {
        match self.functions.get(function) {
            super::identity::FunctionState::Defined { surface, .. } => surface.variadic,
            super::identity::FunctionState::Noted { source } => source.variadic,
            // The body is still cold; the eager stash carries the variadic flag
            // so name resolution scores variadic functions without forcing the
            // body (fz-f98.14.5).
            super::identity::FunctionState::Placeholder => self
                .pending_function_source(function)
                .is_some_and(|source| source.variadic),
        }
    }

    /// The scope walk that populates `function`'s pending source stash, named
    /// as the fact that gates it. `PublishFunctionSource` waits on this scope,
    /// not on `FunctionSource`, so it never waits on the fact it is itself the
    /// sole producer of (fz-f98.14.5). Every returned fact has a producer arm
    /// in `World::demand_fact_producer` (`CodeScoped` -> `Job::ScopeCode`,
    /// `CodeIndexed` -> `Job::IndexCode`, `ModuleDefined` -> `Job::DefineModule`),
    /// so naming the fact is enough — callers do not also need the job.
    ///
    /// For a global-module function, the home code is discovered by scanning
    /// every submitted code unit, so this returns at least one arm-covered
    /// fact whenever any candidate home is still unresolved (`Pending`); it
    /// only returns empty once every code is `Indexed` and none of them is
    /// the home — the terminal dangling case, where the only remaining wait
    /// (`FunctionSourceStash`, which has no producer arm) is legitimate. A
    /// single `Certain` match or `Opaque` item-macro candidate is returned
    /// ALONE (never bundled with the rest of the surface, fz-go4.53): the
    /// scheduler's AND-semantics wake would otherwise force every unrelated
    /// opaque item-macro call in the program to expand before re-checking
    /// whether the wanted name already resolved, so candidates are staged
    /// one `CodeScoped` wait at a time instead.
    /// Diagnoses two (or more) separately submitted codes that both, for
    /// real, define the same top-level `name/arity` — Elixir raises
    /// `CompileError` ("... is already defined") on the same shape,
    /// mirroring `source_publish::duplicate_struct_diagnostic`'s "diagnose
    /// the second occurrence rather than silently keep one" contract. The
    /// span is the SECOND certain home's matching form, a real requester
    /// span rather than `Span::DUMMY`, falling back to the first home's span
    /// only for the (bootstrap-only) `CompilerService` match shape that
    /// carries no form span of its own.
    /// `FunctionDefined`'s sole producer arm is `Job::DefineFunction`
    /// (`World::demand_fact_producer`); this bare wait lets the fact->producer
    /// map restart it instead of naming the job directly.
    pub(crate) fn wait_for_function_definition(&mut self, function: FunctionId) -> JobEffects {
        JobEffects::wait_on_current(FactKey::FunctionDefined(function))
    }

    /// Demands and waits on the module whose definition notes `module`'s
    /// `@type`s — the type-side mirror of `wait_for_function_definition`. Used
    /// only for non-global modules; a top-level type is noted by its code scope.
    /// `ensure_runtime_module` registers the runtime module's source (no eager
    /// enqueue) so a runtime module is minted by the pull that expands this
    /// `ModuleDefined` wait: `ModuleDefined`'s sole producer arm is
    /// `Job::DefineModule`, and `define_module` re-registers the source and
    /// waits on `CodeIndexed(code_id)` (producer arm `Job::IndexCode`), so the
    /// whole chain reaches the minting job through `demand_fact_producer`.
    pub fn fact_revision(&self, key: &FactKey) -> Option<u64> {
        self.work_graph.facts().revision(key)
    }

    #[cfg(test)]
    pub(crate) fn job_reads(&self, job: &Job) -> Option<&HashSet<FactUse<FactKey>>> {
        self.work_graph.reads(job)
    }

    pub fn has_fact(&self, key: &FactKey) -> bool {
        self.work_graph.facts().revision(key).is_some()
    }

    pub fn fact_is_settled(&self, key: &FactKey) -> bool {
        self.work_graph.facts().is_settled(key)
    }

    pub(crate) fn root_entry_executable(&mut self, root: RootId) -> ExecutableKey {
        let entry = self.root_entry(root);
        ExecutableKey {
            activation: self.activation_key(root, entry.function, &entry.input),
            need: entry.need,
        }
    }

    pub(crate) fn scope_lexical_context(
        &self,
        scope: ScopeSnapshot,
        kind: QuotedLexicalContextKind,
    ) -> QuotedLexicalContext {
        let module = self
            .module_name(scope.module_id())
            .map(module_name_segments)
            .unwrap_or_default();
        let function_scope = scope
            .function_id()
            .map(|function| vec![self.function_ref(function).name.clone()])
            .unwrap_or_default();
        QuotedLexicalContext::new(kind, module, function_scope).with_namespace_id(scope.namespace().as_u32())
    }

    pub(crate) fn project_module_value(
        &self,
        builder: &QuotedSourceBuilder,
        scope: ScopeSnapshot,
        kind: QuotedLexicalContextKind,
    ) -> Result<AnyValueRef, QuotedSourceError> {
        let Some(name) = self.module_name(scope.module_id()) else {
            return Ok(builder.nil());
        };
        let metadata = QuotedSourceMetadata {
            lexical_context: Some(self.scope_lexical_context(scope, kind)),
            span: None,
        };
        let segments = name.split('.').collect::<Vec<_>>();
        builder.alias(&metadata, &segments)
    }

    pub(crate) fn project_env_value(
        &self,
        builder: &QuotedSourceBuilder,
        scope: ScopeSnapshot,
        kind: QuotedLexicalContextKind,
    ) -> Result<AnyValueRef, QuotedSourceError> {
        let function = match scope.function_id() {
            Some(function) => {
                let function_ref = self.function_ref(function);
                builder.tuple(&[builder.atom(&function_ref.name), builder.int(function_ref.arity as i64)])?
            }
            None => builder.nil(),
        };
        builder.map(&[
            (builder.atom("module"), self.project_module_value(builder, scope, kind)?),
            (builder.atom("function"), function),
            (
                builder.atom("namespace"),
                builder.int(scope.namespace().as_u32() as i64),
            ),
        ])
    }

    pub(crate) fn require_activation_key_facts(
        &self,
        function: FunctionId,
        reads: &mut Vec<FactKey>,
        waits: &mut HashSet<FactKey>,
    ) -> bool {
        let recursive = FactKey::Recursive(function);
        let recursive_ready = self.has_fact(&recursive);
        if recursive_ready {
            reads.push(recursive);
        } else {
            waits.insert(recursive);
        }

        let dispatch_mask = FactKey::DispatchMask(function);
        let dispatch_mask_ready = self.has_fact(&dispatch_mask);
        if dispatch_mask_ready {
            reads.push(dispatch_mask);
        } else {
            waits.insert(dispatch_mask);
        }

        recursive_ready && dispatch_mask_ready
    }

    pub(crate) fn lookup_callable_namespace(
        &mut self,
        head: Namespace,
        name: &str,
        arity: usize,
    ) -> Option<NamespaceSymbol> {
        if let Some((module_path, local_name)) = name.rsplit_once('.') {
            let module = self.lookup_module_path(head, module_path)?;
            return self.lookup_module_callable(module, local_name, arity);
        }
        self.namespaces
            .lookup_best_matching(head, name, |symbol| match symbol {
                NamespaceSymbol::Function(function)
                | NamespaceSymbol::Macro(function)
                | NamespaceSymbol::Callable(function) => {
                    callable_match_score(self.function_arity(*function), self.function_variadic(*function), arity)
                }
                NamespaceSymbol::Module(_) | NamespaceSymbol::Type(_) | NamespaceSymbol::Splice(_) => None,
            })
            .cloned()
            .map(|symbol| self.resolve_callable_symbol(symbol))
    }

    pub(crate) fn lookup_module_callable(
        &mut self,
        module: ModuleId,
        name: &str,
        arity: usize,
    ) -> Option<NamespaceSymbol> {
        if self.module_interface_revision(module).is_none() {
            return Some(NamespaceSymbol::Callable(self.reference_function(
                module,
                name.to_string(),
                arity,
            )));
        }
        let mut best = None;
        for callable in self.module_interface(module).callables() {
            if callable.reference.name != name {
                continue;
            }
            let Some(score) = callable_match_score(callable.reference.arity, callable.variadic, arity) else {
                continue;
            };
            let replace = best
                .as_ref()
                .is_none_or(|(current, _): &(CallableMatchScore, NamespaceSymbol)| score > *current);
            if replace {
                best = Some((score, callable.namespace_symbol()));
            }
        }
        best.map(|(_, symbol)| symbol)
    }

    fn resolve_callable_symbol(&mut self, symbol: NamespaceSymbol) -> NamespaceSymbol {
        let NamespaceSymbol::Callable(function) = symbol else {
            return symbol;
        };
        let module = self.function_module(function);
        let Some(_) = self.module_interface_revision(module) else {
            return NamespaceSymbol::Callable(function);
        };
        self.module_interface(module)
            .callables()
            .iter()
            .find(|callable| callable.function == function)
            .map(|callable| callable.namespace_symbol())
            .unwrap_or(NamespaceSymbol::Callable(function))
    }

    pub(crate) fn min_variadic_arity(&mut self, head: Namespace, name: &str) -> Option<usize> {
        if let Some((module_path, local_name)) = name.rsplit_once('.') {
            let module = self.lookup_module_path(head, module_path)?;
            self.module_interface_revision(module)?;
            return self
                .module_interface(module)
                .callables()
                .iter()
                .filter(|callable| callable.reference.name == local_name && callable.variadic)
                .map(|callable| callable.reference.arity)
                .min();
        }
        self.namespaces
            .lookup_best_matching(head, name, |symbol| match symbol {
                NamespaceSymbol::Function(function) | NamespaceSymbol::Macro(function)
                    if self.function_variadic(*function) =>
                {
                    Some(Reverse(self.function_arity(*function)))
                }
                _ => None,
            })
            .map(|symbol| match symbol {
                NamespaceSymbol::Function(function) | NamespaceSymbol::Macro(function) => {
                    self.function_arity(*function)
                }
                NamespaceSymbol::Callable(_) => {
                    unreachable!("variadic lookup should not yield unresolved callable expectations")
                }
                NamespaceSymbol::Module(_) | NamespaceSymbol::Type(_) | NamespaceSymbol::Splice(_) => {
                    unreachable!("variadic lookup should not yield modules or types")
                }
            })
    }

    pub(crate) fn guard_dispatch(&self, function: FunctionId) -> PatternGuardDispatch<Ty> {
        #[cfg(test)]
        self.telemetry_query_count.set(self.telemetry_query_count.get() + 1);
        self.guard_dispatches
            .get(function)
            .cloned()
            .expect("guard dispatch should only be read after its fact is defined")
    }

    pub fn code_source(&self, id: CodeId) -> Option<QuotedCodeSource> {
        match self.code.get(id) {
            super::code::CodeState::Indexed { source } | super::code::CodeState::Scoped { source, .. } => {
                Some(source.clone())
            }
            super::code::CodeState::Pending => None,
        }
    }

    pub fn code_surface(&self, id: CodeId) -> Option<&super::quoted_surface::ScopeSurface> {
        match self.code.get(id) {
            super::code::CodeState::Indexed { source } | super::code::CodeState::Scoped { source, .. } => {
                Some(&source.surface)
            }
            super::code::CodeState::Pending => None,
        }
    }

    pub fn module_scope(&self, module: ModuleId) -> Option<(super::identity::ModuleSource, ScopeSnapshot)> {
        match self.modules.get(module) {
            ModuleState::Scoped { source, base, .. } => Some((source.clone(), ScopeSnapshot::module(module, *base))),
            ModuleState::Defined { source, base, .. } => Some((source.clone(), ScopeSnapshot::module(module, *base))),
            _ => None,
        }
    }

    pub fn module_indexed_parent(&self, module: ModuleId) -> Option<(CodeId, ModuleId)> {
        match self.modules.get(module) {
            ModuleState::Indexed { source, .. } => Some((source.code, source.parent)),
            _ => None,
        }
    }

    pub(crate) fn module_named_parent(&mut self, module: ModuleId) -> Option<ModuleId> {
        let name = self.module_name(module)?.to_string();
        let (parent, _) = name.rsplit_once('.')?;
        Some(self.reference_module(parent.to_string()))
    }

    fn module_definition_code(&self, module: ModuleId) -> CodeId {
        match self.modules.get(module) {
            ModuleState::Scoped { source, .. } | ModuleState::Defined { source, .. } => source.code,
            ModuleState::Placeholder { .. } | ModuleState::Indexed { .. } => {
                panic!("modules should be scoped before definition")
            }
        }
    }

    pub(crate) fn canonical_activation_key(
        &mut self,
        root: RootId,
        function: FunctionId,
        inputs: &[Ty],
    ) -> super::identity::ActivationKey {
        let mask = self
            .dispatch_masks
            .get(function)
            .expect("activation keying should wait for dispatch mask facts before activation")
            .clone();
        let keying = *self
            .body_keying
            .get(function)
            .expect("activation keying should wait for recursive facts before activation");
        // The arrow is the PRECISE evidence: address the whole input vector in one
        // pass (fz-hwn.27.6), so two distinct inference vars `[Ty27,Ty28]` address
        // to distinct `[a0,a1]` and never collapse to the phantom `[a0,a0]`.
        let key = super::identity::ActivationKey::from_inputs(root, function, inputs, &mut self.types);
        if !keying.recursive {
            // A non-recursive body that never consumes callable identity only
            // TRANSPORTS the closures that reach it, so closure identity is
            // freight, not meaning: erase the literals from non-dispatch
            // slots and every same-surface brand shares one activation
            // (fz-6gb). A consuming body keeps the precise key -- its
            // specializations buy direct dispatch. Evidence is precise
            // either way.
            if keying.consumes_callable_identity {
                return key;
            }
            let arrow = self.types.erase_transported_closure_identities(key.arrow, &mask);
            return super::identity::ActivationKey { arrow, ..key };
        }
        // Bounded specialization (fz-y6w): the dispatch KEY is a whole-arrow
        // convergence collapse of that evidence — recursive non-dispatch slots
        // widen to their convergence class so the ascent settles. Key != evidence
        // is intentional; the precise arrow stays in `ActivationInputs`.
        let arrow = self.types.convergence_collapse(key.arrow, &mask);
        super::identity::ActivationKey { arrow, ..key }
    }

    pub(crate) fn closure_ty(&mut self, function: FunctionId, captures: Vec<Ty>) -> Ty {
        let arity = self.functions.reference_for(function).arity;
        self.types
            .closure_lit(ClosureTarget(function.as_u32()), captures, arity)
    }

    fn qualified_module_name(&self, parent: ModuleId, local_name: &str) -> String {
        if parent.is_global() {
            local_name.to_string()
        } else {
            let parent_name = self
                .modules
                .name(parent)
                .expect("named parent module should have a reverse lookup");
            format!("{parent_name}.{local_name}")
        }
    }

    /// The `Ty` a `defimpl P, for: Target` module contributes to protocol
    /// dispatch, from a typed classification of `Target` rather than
    /// last-segment string matching: a struct backed by `StructDefined`
    /// (`reads` records the fact so incremental re-derivation can depend on
    /// it), one of the compiler's built-in ground value families, or a bare
    /// nominal target that is neither.
    pub(crate) fn module_impl_target_ty(&mut self, module: ModuleId, reads: &mut Vec<FactKey>) -> Ty {
        self.module_impl_target_ty_with(module, reads)
    }

    pub(crate) fn struct_value_ty(&mut self, module_name: &str, field_names: &[String], field_tys: &[Ty]) -> Ty {
        debug_assert_eq!(
            field_names.len(),
            field_tys.len(),
            "struct type fields must be ordered against their schema"
        );
        let tag = format!("impl-target::{}", module_name.rsplit('.').next().unwrap_or(module_name));
        let nominal = self.types.opaque_of(&tag);
        let tuple = self.types.tuple(field_tys);
        let map_fields = field_names
            .iter()
            .zip(field_tys.iter().copied())
            .map(|(name, ty)| (MapKey::Atom(name.clone()), ty))
            .collect::<Vec<_>>();
        let map = self.types.map(&map_fields);
        let structural = self.types.union(tuple, map);
        self.types.union(nominal, structural)
    }

    pub(crate) fn resolve_module_name(
        &mut self,
        current_module: ModuleId,
        head: Namespace,
        path: &crate::modules::identity::ModuleName,
    ) -> Option<ModuleId> {
        if path.segments().len() == 1 {
            let local = path.last_segment();
            if let Some(NamespaceSymbol::Module(module)) = self.lookup_namespace(head, local) {
                return Some(module);
            }
            if current_module.is_global() {
                return Some(self.reference_module(local.to_string()));
            }
            let current_name = self.module_name(current_module)?;
            if current_name.rsplit('.').next().unwrap_or(current_name) == local {
                return Some(current_module);
            }
            return Some(self.reference_module(path.dotted()));
        }

        let dotted = path.dotted();
        self.lookup_module_path(head, &dotted)
            .or_else(|| Some(self.reference_module(dotted)))
    }

    pub(crate) fn lookup_module_path(&mut self, head: Namespace, path: &str) -> Option<ModuleId> {
        let mut segments = path.split('.');
        let first = segments.next()?;
        let mut module = match self.namespaces.lookup(head, first) {
            Some(NamespaceSymbol::Module(module)) => *module,
            _ => return None,
        };
        for segment in segments {
            module = self.reference_child_module(module, segment);
        }
        Some(module)
    }

    fn module_impl_target_ty_with(&mut self, module: ModuleId, reads: &mut Vec<FactKey>) -> Ty {
        let name = self
            .module_name(module)
            .expect("impl target modules should have reverse names")
            .to_string();
        match self.classify_impl_target(module, &name, reads) {
            ImplTargetKind::Struct => {
                // Honor the struct's declared @type field types for the dispatch
                // target too (fz-f98.8/f98.10): a `vec![any]` target erases the
                // element at the protocol boundary, so intersecting a concrete
                // receiver against it cannot recover the element type.
                if let Some(declared) = self.declared_struct_value_ty(module) {
                    declared
                } else {
                    let field_names = self
                        .struct_def(module)
                        .expect("classify_impl_target proved this module has a StructDef")
                        .fields
                        .clone();
                    let any = self.types.any();
                    let field_tys = vec![any; field_names.len()];
                    self.struct_module_value_ty(module, &field_names, &field_tys)
                }
            }
            ImplTargetKind::Builtin(family) => builtin_value_family_ty(&mut self.types, family),
            ImplTargetKind::Nominal => nominal_impl_target_ty(&mut self.types, &name),
        }
    }

    /// Classifies a protocol impl target module by fact, not by string: a
    /// struct wins whenever `StructDefined(module)` has published one,
    /// otherwise the name is checked against the compiler's built-in ground
    /// value families (`List`/`Integer`/`Float`/`Atom`/`Binary`/`Map` — these
    /// have no backing module facts at all, the name literally *is* their
    /// identity), and anything left over is a bare nominal target (e.g.
    /// `defimpl P, for: String`, where `String` names no struct and no ground
    /// family).
    ///
    /// The subscription on `StructDefined(module)` is registered
    /// UNCONDITIONALLY — before the struct-first branch, covering every return
    /// path — because the classification DEPENDS on whether the struct is
    /// defined: a target forward-referenced before its `defstruct` settles
    /// reads `struct_def(module) == None` this round and falls through to
    /// Builtin/Nominal, and only the recorded read wakes this job to
    /// reclassify it to Struct once `StructDefined(module)` publishes (the
    /// scheduler invariant: a producer subscribes to every fact its conclusion
    /// read, including ones absent at read time). This is the same discipline
    /// `resolve_protocol_call` uses for `ProtocolImplProviders`. It stays a
    /// `reads` subscription rather than a hard `waits` block, so a bare
    /// builtin/nominal name that never publishes `StructDefined` classifies
    /// immediately and does not stall.
    fn classify_impl_target(&mut self, module: ModuleId, name: &str, reads: &mut Vec<FactKey>) -> ImplTargetKind {
        reads.push(FactKey::StructDefined(module));
        if self.struct_def(module).is_some() {
            return ImplTargetKind::Struct;
        }
        match BuiltinValueFamily::from_name(name) {
            Some(family) => ImplTargetKind::Builtin(family),
            None => ImplTargetKind::Nominal,
        }
    }

    /// The struct type projected from an already-resolved field schema
    /// (`field_names`/`field_tys` in schema order): the shared tail of both
    /// `struct_assertion_ty` (schema read from `struct_def`) and struct-literal
    /// type inference (schema read from the lowered field list, already
    /// ordered against `struct_def_fields` by body lowering).
    pub(crate) fn struct_module_value_ty(&mut self, module: ModuleId, field_names: &[String], field_tys: &[Ty]) -> Ty {
        let name = self
            .module_name(module)
            .unwrap_or_else(|| panic!("named struct module {} should have a reverse lookup", module.as_u32()))
            .to_string();
        self.struct_value_ty(&name, field_names, field_tys)
    }

    fn unresolved_issues(&self, waits: &[UnresolvedWait<Job, FactKey>]) -> Vec<UnresolvedIssue> {
        let frontier = waits
            .iter()
            .map(|wait| wait.fact.clone().into_fact())
            .collect::<HashSet<_>>();
        let mut issues = Vec::new();
        for wait in waits {
            if let Some(issue) = self.unresolved_issue(&frontier, wait.fact.fact()) {
                issues.push(issue);
            }
        }
        issues.sort_by_key(|issue| match issue.key {
            UnresolvedIssueKey::Module(module) => (0_u8, module.as_u32()),
            UnresolvedIssueKey::Struct(module) => (1_u8, module.as_u32()),
            UnresolvedIssueKey::Function(function) => (2_u8, function.as_u32()),
            UnresolvedIssueKey::Export(function) => (3_u8, function.as_u32()),
        });
        issues.dedup_by_key(|issue| issue.key);
        issues
    }

    fn unresolved_issue(&self, frontier: &HashSet<FactKey>, fact: &FactKey) -> Option<UnresolvedIssue> {
        match fact {
            FactKey::ModuleIndexed(module) => Some(self.unresolved_module_issue(*module)),
            FactKey::StructDefined(module) => self.unresolved_struct_issue(*module),
            FactKey::FunctionSource(function) => self.unresolved_function_issue(frontier, *function),
            FactKey::ExpandedFunctionSource(function) => self.unresolved_function_issue(frontier, *function),
            FactKey::FunctionDefined(function) => self.unresolved_function_issue(frontier, *function),
            _ => None,
        }
    }

    /// A `StructDefined(module)` wait that survives to the terminal frontier
    /// means the drive drained without that fact publishing — so `%module{}`
    /// named something that never produces a `defstruct`. If the module is
    /// still wholly unresolved, its own module-not-defined issue speaks (return
    /// `None` here to avoid double-reporting); if it settled (a plain
    /// `defmodule`, a builtin/runtime module) but carries no `defstruct`, then
    /// `%module{}` is a real user error — reported at the referencing span the
    /// obligation carries, turning what would otherwise be a silent stall into
    /// a terminating diagnostic.
    fn unresolved_struct_issue(&self, module: ModuleId) -> Option<UnresolvedIssue> {
        if self.module_defined_revision(module).is_none() && !self.is_runtime_module(module) {
            return None;
        }
        let span = self
            .struct_expectations
            .reference_expectations(module)
            .first()
            .map(|expectation| expectation.requester.span)
            .unwrap_or(Span::DUMMY);
        let module_name = self
            .module_name(module)
            .map(str::to_owned)
            .unwrap_or_else(|| format!("<unnamed module {}>", module.as_u32()));
        Some(UnresolvedIssue {
            key: UnresolvedIssueKey::Struct(module),
            diagnostic: Diagnostic::error(
                codes::RESOLVE_NOT_A_STRUCT,
                format!("module `{}` is not a struct", module_name),
                span,
            ),
        })
    }

    /// The span comes from the first bare `import`/`require` that named
    /// `module` before it resolved (`note_module_reference_expectation`),
    /// the same `.first()`-of-recorded-obligations discipline
    /// `unresolved_struct_issue` uses for `struct_expectations`. A module
    /// that stalled without ever picking up such a reference (e.g. a named
    /// root submitted by an external caller, not a source reference) has
    /// none recorded, and falls back to `Span::DUMMY` -- there genuinely is
    /// no reference site to name.
    fn unresolved_module_issue(&self, module: ModuleId) -> UnresolvedIssue {
        let span = self
            .module_reference_expectations
            .expectations(module)
            .first()
            .map(|expectation| expectation.requester.span)
            .unwrap_or(Span::DUMMY);
        UnresolvedIssue {
            key: UnresolvedIssueKey::Module(module),
            diagnostic: Diagnostic::error(
                codes::RESOLVE_UNKNOWN_MODULE,
                format!(
                    "module `{}` is not defined",
                    self.module_name(module)
                        .expect("referenced modules should have reverse names")
                ),
                span,
            ),
        }
    }

    fn unresolved_function_issue(&self, frontier: &HashSet<FactKey>, function: FunctionId) -> Option<UnresolvedIssue> {
        let function_ref = self.function_ref(function);
        if function_ref.module.is_global() {
            // No `Span::DUMMY` fallback to fix here: a global-module function
            // that never resolves reaches this arm exclusively through
            // `submit_root` naming an entry point by string (the compiler's
            // external front door, not a source reference) -- every in-source
            // call to a name `lookup_callable_namespace` cannot find fails
            // immediately at lowering time with its own real span
            // (`World::unbound_runtime_function`), never reaching the stall
            // detector at all. There is no reference site to name here.
            return Some(UnresolvedIssue {
                key: UnresolvedIssueKey::Function(function),
                diagnostic: Diagnostic::error(
                    codes::RESOLVE_UNKNOWN_FUNCTION,
                    format!("function `{}/{}` is not defined", function_ref.name, function_ref.arity),
                    Span::DUMMY,
                ),
            });
        }

        if self.module_defined_revision(function_ref.module).is_none()
            && !self.module_has_source_state(function_ref.module)
            && !self.is_runtime_module(function_ref.module)
            && self.module_interface_revision(function_ref.module).is_none()
        {
            return Some(self.unresolved_module_issue(function_ref.module));
        }

        if frontier.contains(&FactKey::ModuleIndexed(function_ref.module))
            || self.module_defined_revision(function_ref.module).is_none()
        {
            return None;
        }

        let module_name = self
            .module_name(function_ref.module)
            .expect("referenced function modules should have reverse names");
        // The span comes from the `InterfaceExpectation` `resolve_runtime_function`
        // recorded for this exact `(name, arity)` when the call was lowered
        // (`reference_module_interface_callable`). `validate_module_interface_expectations`
        // normally catches this mismatch the moment the module's own interface
        // settles; this arm is reached only when the expectation was recorded
        // *after* that validation already ran, so it survives unvalidated to
        // the terminal frontier -- the same late-obligation shape
        // `unresolved_struct_issue` handles for `struct_expectations`.
        let span = self
            .module_interface_if_present(function_ref.module)
            .and_then(|interface| {
                interface
                    .expectations()
                    .iter()
                    .find(|expectation| {
                        expectation.name == function_ref.name && expectation.arity == function_ref.arity
                    })
                    .and_then(|expectation| expectation.requester.as_ref())
                    .map(|requester| requester.span)
            })
            .unwrap_or(Span::DUMMY);
        Some(UnresolvedIssue {
            key: UnresolvedIssueKey::Export(function),
            diagnostic: Diagnostic::error(
                codes::RESOLVE_UNKNOWN_IMPORT,
                format!(
                    "module `{}` does not export `{}/{}`",
                    module_name, function_ref.name, function_ref.arity
                ),
                span,
            ),
        })
    }
}

fn emit_job_diagnostic(tel: &impl Telemetry, diagnostic: Diagnostic) -> FatalError {
    emit_through(tel, std::slice::from_ref(&diagnostic));
    FatalError
}

/// Drop repeats, keep the order the job emitted them in.
///
/// A job may name the same fact twice; the fact table refuses duplicates, so
/// they are dropped here. What must NOT be dropped is the order: a job's
/// emission order becomes the order its dependents wake, which becomes the
/// order fresh types reach the interner. Deduping through a `HashSet` scrambled
/// every job's outputs at the one place they all funnel through, which is how
/// two compiles of the same input published different raw `Ty` numbering
/// (fz-f98.19).
fn dedupe_job_facts(facts: Vec<FactKey>) -> Vec<FactKey> {
    facts.into_iter().collect::<OrderedSet<_>>().iter().cloned().collect()
}

fn callable_match_score(fixed_arity: usize, variadic: bool, actual_arity: usize) -> Option<CallableMatchScore> {
    if fixed_arity == actual_arity {
        return Some(CallableMatchScore::Exact);
    }
    if variadic && fixed_arity <= actual_arity {
        return Some(CallableMatchScore::VariadicPrefix(fixed_arity));
    }
    None
}

/// How definitively a code's surface, still `Indexed` (not yet scoped), could
/// turn out to publish a wanted global function. Declaration order IS rank
/// order (derived `Ord`): `None < Opaque < Certain`, so `.max()` over a
/// code's forms picks the most definitive verdict any single form gives.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum FunctionSurfaceMatch {
    /// This code's surface rules the function out entirely.
    None,
    /// An unexpanded item-macro call whose head is not reserved: its
    /// expansion is unknown until it runs, so it is only a MAYBE home.
    Opaque,
    /// A plain `fn`/`fnp`/`defmacro`/`defmodule`/`defprotocol`/`defimpl` head
    /// names the wanted name+arity statically: scoping this code is
    /// guaranteed to publish the function (or the reference is to a form
    /// scoping cannot change its mind about).
    Certain,
}

fn code_surface_function_match(source: &QuotedCodeSource, function_ref: &FunctionRef) -> FunctionSurfaceMatch {
    source
        .surface
        .forms
        .iter()
        .map(|form| match form {
            ScopeForm::Function(function)
                if function.name == function_ref.name && function.arity == function_ref.arity =>
            {
                FunctionSurfaceMatch::Certain
            }
            ScopeForm::Function(_) => FunctionSurfaceMatch::None,
            ScopeForm::CompilerService(service) => {
                if source_definition_matches_function(&service.source, function_ref) {
                    FunctionSurfaceMatch::Certain
                } else {
                    FunctionSurfaceMatch::None
                }
            }
            ScopeForm::MacroCall(macro_call) => item_macro_call_match(&macro_call.source, function_ref),
            ScopeForm::Alias(_)
            | ScopeForm::Import(_)
            | ScopeForm::Require(_)
            | ScopeForm::Module(_)
            | ScopeForm::Protocol(_)
            | ScopeForm::ProtocolImpl(_)
            | ScopeForm::Struct(_) => FunctionSurfaceMatch::None,
        })
        // `Certain` beats `Opaque` beats `None`: one certain form is enough to
        // call the whole code a certain home even if it also contains
        // unrelated opaque macro calls.
        .max()
        .unwrap_or(FunctionSurfaceMatch::None)
}

/// The span of `function_ref`'s matching `fn`/`fnp`/`defmacro` form in
/// `source`'s top-level surface, when it has one — a plain `ScopeForm::Function`
/// always carries a real source span (`quoted_surface::FunctionForm::span`);
/// the `CompilerService` match shape (bootstrap-only) does not carry a form
/// span of its own, so it returns `None` rather than `Span::DUMMY` here, and
/// the caller falls back to another candidate's span instead.
fn function_form_span(source: &QuotedCodeSource, function_ref: &FunctionRef) -> Option<Span> {
    source.surface.forms.iter().find_map(|form| match form {
        ScopeForm::Function(function) if function.name == function_ref.name && function.arity == function_ref.arity => {
            Some(function.span)
        }
        _ => None,
    })
}

fn source_definition_matches_function(source: &QuotedSourceRoot, function_ref: &FunctionRef) -> bool {
    matches!(
        reserved_source_definition(source).ok().flatten(),
        Some(ReservedSourceDefinition::Function { name, arity, .. })
            if name == function_ref.name && arity == function_ref.arity
    )
}

/// How definitively an unexpanded item-level macro call could turn out to be
/// the home of `function_ref`. A reserved head (`fn`/`fnp`/`defmacro`/
/// `defmodule`/`defprotocol`/`defimpl`) names its target statically, so a
/// definite mismatch rules the call out for good (same rule as
/// `source_definition_matches_function`) and a match is `Certain`. Any other
/// head is a call to a user-defined `defmacro`: its expansion is unknown
/// until it actually runs, so the call is only an `Opaque` candidate home for
/// every still-unresolved global name. Treating it as a non-match here would
/// strand a macro-produced root or callee name behind a wait no producer arm
/// ever wakes (the arm-less `FunctionSourceStash` fallback in
/// `demand_function_scope`), since nothing would ever demand the `ScopeCode`
/// that expands the macro and stashes the name it produces.
fn item_macro_call_match(source: &QuotedSourceRoot, function_ref: &FunctionRef) -> FunctionSurfaceMatch {
    match reserved_source_definition(source) {
        Ok(Some(ReservedSourceDefinition::Function { name, arity, .. })) => {
            if name == function_ref.name && arity == function_ref.arity {
                FunctionSurfaceMatch::Certain
            } else {
                FunctionSurfaceMatch::None
            }
        }
        Ok(Some(_)) => FunctionSurfaceMatch::None,
        Ok(None) | Err(_) => FunctionSurfaceMatch::Opaque,
    }
}

/// A consumer's references are a set: the same type named twice (e.g. by both a
/// spec and a parameter annotation) is one dependency. Order is preserved.
fn dedup_type_names(refs: &mut Vec<TypeName>) {
    let mut seen = HashSet::new();
    refs.retain(|name| seen.insert(name.clone()));
}

/// The struct-ref sibling of `dedup_type_names`: the same struct module named
/// twice in one `@type` body (e.g. two fields of the same struct type) is one
/// wait, not two.
fn dedup_module_ids(refs: &mut Vec<ModuleId>) {
    let mut seen = HashSet::new();
    refs.retain(|module| seen.insert(*module));
}

fn module_name_segments(name: &str) -> Vec<String> {
    name.split('.')
        .filter(|segment| !segment.is_empty())
        .map(str::to_string)
        .collect()
}

/// The typed shape a `defimpl P, for: Target` module classifies as. See
/// `World::classify_impl_target` for how this is derived — the point of
/// having this type is that dispatch resolution matches on a closed enum
/// instead of re-deriving the same three cases from a module name string.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ImplTargetKind {
    /// `StructDefined(module)` published a schema: the dispatch target is
    /// this struct's nominal identity plus tuple/map field evidence.
    Struct,
    /// One of the compiler's built-in ground value families. These carry no
    /// module facts at all — the name is their entire identity.
    Builtin(BuiltinValueFamily),
    /// Neither of the above: a bare module name used only as a protocol
    /// target tag (e.g. `defimpl P, for: String`), projected to an opaque
    /// nominal type.
    Nominal,
}

/// The compiler's built-in ground value families: primitive value shapes a
/// protocol can dispatch on by name alone, with no `defstruct` and (for
/// `Integer`/`Float`/`Atom`/`Binary`) no backing module source at all.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BuiltinValueFamily {
    List,
    Integer,
    Float,
    Atom,
    Binary,
    Map,
}

impl BuiltinValueFamily {
    fn from_name(module_name: &str) -> Option<Self> {
        match module_name.rsplit('.').next().unwrap_or(module_name) {
            "List" => Some(Self::List),
            "Integer" => Some(Self::Integer),
            "Float" => Some(Self::Float),
            "Atom" => Some(Self::Atom),
            "Binary" => Some(Self::Binary),
            "Map" => Some(Self::Map),
            _ => None,
        }
    }
}

fn builtin_value_family_ty<T: crate::types::Types<Ty = Ty>>(t: &mut T, family: BuiltinValueFamily) -> Ty {
    match family {
        BuiltinValueFamily::List => {
            let any = t.any();
            t.list(any)
        }
        BuiltinValueFamily::Integer => t.int(),
        BuiltinValueFamily::Float => t.float(),
        BuiltinValueFamily::Atom => t.atom(),
        BuiltinValueFamily::Binary => t.str_t(),
        BuiltinValueFamily::Map => t.map_top(),
    }
}

fn nominal_impl_target_ty<T: crate::types::Types<Ty = Ty>>(t: &mut T, module_name: &str) -> Ty {
    let tag = module_name.rsplit('.').next().unwrap_or(module_name);
    t.opaque_of(&format!("impl-target::{}", tag))
}

impl World {
    fn register_code(&mut self, name: Option<String>, text: String) -> CodeId {
        self.code.define(name, text)
    }

    pub fn submit_code(&mut self, name: Option<String>, text: String) -> CodeId {
        let code_id = self.register_code(name, text);
        self.work_graph
            .enqueue(Job::IndexCode(code_id), WorkStartReason::Ignition);
        if !self.roots.is_empty() {
            self.work_graph
                .enqueue(Job::ScopeCode(code_id), WorkStartReason::Ignition);
        }
        code_id
    }

    pub fn submit_root(
        &mut self,
        module_name: Option<String>,
        name: String,
        arity: usize,
        need: ExecutableNeed,
    ) -> RootId {
        let module = module_name
            .as_deref()
            .map(|name| self.reference_module(name.to_string()))
            .unwrap_or(ModuleId::GLOBAL);
        let function = self.reference_function(module, name, arity);
        let any = self.types.any();
        let root_id = self.roots.define(RootEntry {
            function,
            input: vec![any; arity],
            need,
            kind: RootKind::Runtime,
        });
        self.work_graph
            .enqueue(Job::SeedRoot(root_id), WorkStartReason::Ignition);
        root_id
    }

    fn take_unresolved_diagnostics(&mut self, waits: &[UnresolvedWait<Job, FactKey>]) -> Vec<Diagnostic> {
        let issues = self.unresolved_issues(waits);
        let next = issues.iter().map(|issue| issue.key).collect::<HashSet<_>>();
        let diagnostics = issues
            .into_iter()
            .filter(|issue| !self.reported_unresolved.contains(&issue.key))
            .map(|issue| issue.diagnostic)
            .collect();
        self.reported_unresolved = next;
        diagnostics
    }

    fn take_reported_warnings(&mut self) -> Vec<Diagnostic> {
        self.warning_diagnostics.sort_by(|left, right| {
            let left_span = left.primary.span;
            let right_span = right.primary.span;
            left_span
                .code_id
                .0
                .cmp(&right_span.code_id.0)
                .then(left_span.start.cmp(&right_span.start))
                .then(left_span.end.cmp(&right_span.end))
                .then(left.code.0.cmp(right.code.0))
                .then(left.message.cmp(&right.message))
        });
        std::mem::take(&mut self.warning_diagnostics)
    }

    pub fn define_activation_analysis(&mut self, key: &ActivationKey, analysis: ActivationAnalysis) -> bool {
        self.activations.define_analysis(key, analysis)
    }

    pub fn define_activation_return(&mut self, key: &ActivationKey, evidence: Option<Ty>) -> bool {
        self.define_activation_return_outcome(key, evidence).changed
    }

    fn define_activation_return_outcome(
        &mut self,
        key: &ActivationKey,
        evidence: Option<Ty>,
    ) -> super::semantic::ReturnDefine {
        let rebased = self.work_graph.rebased(&Job::AnalyzeActivation(key.clone()));
        self.activations.define_return(&mut self.types, key, evidence, rebased)
    }

    pub fn define_callsite_summary(&mut self, key: CallSiteKey, mut summary: CallSiteSummary) -> bool {
        for target in &mut summary.targets {
            target.surface_inputs = self.types.address_inputs(&target.surface_inputs);
        }
        self.callsites.define(&mut self.types, key, summary)
    }

    pub(crate) fn define_backend_program(&mut self, root: RootId, program: BackendProgram) -> bool {
        self.backend.define(root, program)
    }

    pub(crate) fn define_macro_executable(
        &mut self,
        function: FunctionId,
        root: RootId,
        backend_revision: u64,
        program: BackendProgram,
    ) -> bool {
        self.macro_executables.define(
            function,
            MacroExecutable {
                root,
                backend_revision,
                program,
            },
        )
    }

    pub(crate) fn define_native_program(&mut self, root: RootId, program: NativeProgram) -> bool {
        self.native.define(root, program)
    }

    pub(crate) fn run_macro_on_source_with(
        &mut self,
        function: FunctionId,
        source: &QuotedSourceRoot,
        caller: AnyValueRef,
        args: &[AnyValueRef],
        run: impl FnOnce(
            &mut Types,
            &TransportStore,
            &BackendProgram,
            fz_runtime::process::Process,
            Vec<RuntimeValue>,
        ) -> (fz_runtime::process::Process, Result<RuntimeValue, String>),
    ) -> Result<QuotedSourceRoot, String> {
        let executable = self
            .macro_executable(function)
            .ok_or_else(|| format!("macro {} is not executable", function.as_u32()))?
            .clone();
        let mut semantic_values = Vec::with_capacity(1 + args.len());
        semantic_values.push(RuntimeValue::Ref(caller));
        semantic_values.extend(args.iter().copied().map(RuntimeValue::Ref));
        let runtime_args =
            crate::ir_interp::encode_macro_entry_inputs(&executable.program, &self.transport, &semantic_values)?;
        let value = source.lend_process(|process| {
            run(
                &mut self.types,
                &self.transport,
                &executable.program,
                process,
                runtime_args,
            )
        })?;
        match value {
            RuntimeValue::Ref(root) => Ok(source.subroot(root)),
            other => Err(format!(
                "macro {} returned non-source value {}",
                function.as_u32(),
                other.render(std::ptr::null_mut())
            )),
        }
    }

    pub fn define_module(&mut self, id: ModuleId, base: Namespace, interface: ModuleInterface) -> bool {
        let code = self.module_definition_code(id);
        self.modules.define(id, code, base, interface)
    }

    fn module_interface_diagnostic(&self, id: ModuleId, interface: &ModuleInterface) -> Option<Diagnostic> {
        let expectation = interface.expectations().iter().find(|expectation| {
            !interface
                .callables()
                .iter()
                .any(|callable| expectation.matches_callable(callable))
        })?;
        let module_name = self
            .module_name(id)
            .map(str::to_owned)
            .unwrap_or_else(|| format!("<unnamed module {}>", id.as_u32()));
        let message = match expectation.kind {
            InterfaceCallableKind::Macro => format!(
                "module `{}` does not export macro `{}/{}`",
                module_name, expectation.name, expectation.arity
            ),
            InterfaceCallableKind::PublicFunction | InterfaceCallableKind::Callable => format!(
                "module `{}` does not export `{}/{}`",
                module_name, expectation.name, expectation.arity
            ),
        };
        Some(Diagnostic::error(
            codes::RESOLVE_UNKNOWN_IMPORT,
            message,
            expectation
                .requester
                .as_ref()
                .map(|requester| requester.span)
                .unwrap_or(Span::DUMMY),
        ))
    }

    pub fn note_type_decl(&mut self, name: &TypeName, decl: NotedTypeDecl) -> bool {
        self.type_decls.note(name.clone(), decl)
    }

    pub(crate) fn record_function_type_refs(&mut self, function: &FunctionId, mut refs: Vec<TypeName>) -> bool {
        dedup_type_names(&mut refs);
        self.type_refs.record_function(*function, refs)
    }

    pub(crate) fn record_type_def_refs(&mut self, name: &TypeName, mut refs: Vec<TypeName>) -> bool {
        dedup_type_names(&mut refs);
        self.type_refs.record_type(name, refs)
    }

    pub(crate) fn define_type_def(&mut self, name: &TypeName, def: TypeDef) -> bool {
        self.type_defs.define(name.clone(), def)
    }

    pub(crate) fn define_struct_def(&mut self, module: ModuleId, def: StructDef) -> bool {
        self.struct_defs.define(module, def)
    }

    pub(crate) fn note_struct_field_expectation(
        &mut self,
        module: ModuleId,
        field: String,
        requester: InterfaceRequester,
    ) {
        self.struct_expectations
            .record_field(module, StructFieldExpectation { field, requester });
    }

    fn struct_field_diagnostics(&self, module: ModuleId) -> Vec<Diagnostic> {
        let Some(def) = self.struct_defs.get(module) else {
            return Vec::new();
        };
        self.struct_expectations
            .field_expectations(module)
            .iter()
            .filter(|expectation| !def.fields.iter().any(|field| field == &expectation.field))
            .map(|expectation| {
                let module_name = self
                    .module_name(module)
                    .map(str::to_owned)
                    .unwrap_or_else(|| format!("<unnamed module {}>", module.as_u32()));
                Diagnostic::error(
                    codes::RESOLVE_UNKNOWN_STRUCT_FIELD,
                    format!("struct `{}` has no field `{}`", module_name, expectation.field),
                    expectation.requester.span,
                )
            })
            .collect()
    }

    pub(crate) fn define_protocol_dispatch(&mut self, protocol: ModuleId, dispatch: ProtocolDispatch) -> bool {
        self.protocol_dispatches.define(protocol, dispatch)
    }

    pub(crate) fn refresh_protocol_dispatch(&mut self, protocol: ModuleId) -> bool {
        let dispatch = ProtocolDispatch {
            arms: self
                .protocol_impls_for(protocol)
                .into_iter()
                .map(|(key, protocol_impl)| ProtocolDispatchArm {
                    target: key.target,
                    callbacks: protocol_impl.callbacks,
                })
                .collect(),
        };
        self.define_protocol_dispatch(protocol, dispatch)
    }
}

impl World {
    pub(crate) fn define_function(
        &mut self,
        id: FunctionId,
        source: FunctionSource,
        expanded_source: FunctionSource,
        surface: FunctionSurface,
    ) -> bool {
        self.functions.define(id, source, expanded_source, surface)
    }

    pub(crate) fn stash_function_source(&mut self, function: FunctionId, source: FunctionSource) -> bool {
        self.pending_function_sources.stash(function, source)
    }

    pub(crate) fn publish_pending_function_source(&mut self, function: FunctionId) -> Option<bool> {
        let source = self.pending_function_sources.get(function).cloned()?;
        Some(self.note_function_source(function, source))
    }

    pub(crate) fn note_function_source(&mut self, function: FunctionId, source: FunctionSource) -> bool {
        self.functions.note(function, source)
    }

    pub(crate) fn note_expanded_function_source(&mut self, function: FunctionId, source: FunctionSource) -> bool {
        self.expanded_function_sources.define(function, source)
    }

    pub(crate) fn define_function_contract(&mut self, function: FunctionId, contract: FunctionContract) -> bool {
        self.function_contracts.define(function, contract)
    }

    pub(crate) fn define_protocol_callback(&mut self, function: &FunctionId, protocol: &ModuleId) {
        self.protocol_callbacks
            .define(*function, ProtocolCallback { protocol: *protocol });
    }

    pub(crate) fn define_protocol_impl(
        &mut self,
        protocol: &ModuleId,
        target: &ModuleId,
        callbacks: HashMap<FunctionId, ProtocolCallbackImpl>,
    ) {
        self.protocol_impls.define(
            ProtocolImplKey {
                protocol: *protocol,
                target: *target,
            },
            ProtocolImpl { callbacks },
        );
    }

    pub(crate) fn define_generated_function(
        &mut self,
        owner: FunctionId,
        namespace: Namespace,
        capture_params: Vec<String>,
        surface: FunctionSurface,
    ) -> (FunctionId, bool) {
        let (owner_source, _) = self.function_definition(owner);
        let owner_module = self.functions.reference_for(owner).module;
        let id = self
            .functions
            .reference_generated(owner, owner_module, surface.span, surface.arity());
        let fn_source = FunctionSource {
            code: owner_source.code,
            owner_module: owner_source.owner_module,
            namespace,
            capture_params,
            required_remote_macros: owner_source.required_remote_macros.clone(),
            variadic: surface.variadic,
            source: owner_source.source,
        };
        let changed = self.functions.define(id, fn_source.clone(), fn_source, surface);
        (id, changed)
    }

    pub(crate) fn define_lowered_body(&mut self, function: FunctionId, body: LoweredBody) -> bool {
        self.bodies.define(function, body)
    }

    pub(crate) fn define_guard_dispatch(&mut self, function: FunctionId, dispatch: PatternGuardDispatch<Ty>) -> bool {
        self.guard_dispatches.define(function, dispatch)
    }

    pub(crate) fn define_entry_dispatch(&mut self, function: FunctionId, plan: PatternDispatchPlan<Ty>) -> bool {
        self.entry_dispatches.define(function, plan)
    }

    pub(crate) fn ensure_runtime_module(&mut self, module: ModuleId) -> Option<CodeId> {
        self.ensure_runtime_module_registration(module)
            .map(|registration| registration.code_id)
    }

    fn ensure_runtime_module_registration(&mut self, module: ModuleId) -> Option<RuntimeModuleRegistration> {
        let slot = self.runtime_modules.get(&module)?;
        if let Some(code_id) = slot.code_id {
            return Some(RuntimeModuleRegistration {
                code_id,
                inserted: false,
            });
        }
        let code_id = self.register_code(Some(format!("runtime:{}.fz", slot.name)), slot.source.to_string());
        self.runtime_modules
            .get_mut(&module)
            .expect("runtime module should still exist while recording its code id")
            .code_id = Some(code_id);
        Some(RuntimeModuleRegistration {
            code_id,
            inserted: true,
        })
    }

    fn wait_for_type_decl_registration(&mut self, module: ModuleId) -> (JobEffects, Option<RuntimeModuleRegistration>) {
        let registration = self.ensure_runtime_module_registration(module);
        (
            JobEffects::wait_on_current(FactKey::ModuleDefined(module)),
            registration,
        )
    }

    pub(crate) fn demand_function_scope(&mut self, function: FunctionId) -> Result<Vec<FactKey>, Box<Diagnostic>> {
        let module = self.function_module(function);
        if module.is_global() {
            let function_ref = self.function_ref(function).clone();
            let mut certain_homes = Vec::new();
            let mut opaque_candidates = Vec::new();
            let mut pending = Vec::new();
            for code_id in self.code.ids() {
                match self.code.get(code_id) {
                    CodeState::Pending => pending.push(FactKey::CodeIndexed(code_id)),
                    CodeState::Indexed { source } => match code_surface_function_match(source, &function_ref) {
                        FunctionSurfaceMatch::Certain => certain_homes.push(code_id),
                        FunctionSurfaceMatch::Opaque => opaque_candidates.push(code_id),
                        FunctionSurfaceMatch::None => {}
                    },
                    CodeState::Scoped { .. } => {}
                }
            }
            if certain_homes.len() > 1 {
                return Err(Box::new(
                    self.duplicate_function_diagnostic(&function_ref, &certain_homes),
                ));
            }
            if let Some(code_id) = certain_homes.into_iter().next() {
                return Ok(vec![FactKey::CodeScoped(code_id)]);
            }
            if let Some(code_id) = opaque_candidates.into_iter().next() {
                return Ok(vec![FactKey::CodeScoped(code_id)]);
            }
            return Ok(pending);
        }
        if self.module_has_source_state(module) || self.ensure_runtime_module(module).is_some() {
            return Ok(vec![FactKey::ModuleDefined(module)]);
        }
        Ok(Vec::new())
    }

    fn duplicate_function_diagnostic(&self, function_ref: &FunctionRef, certain_homes: &[CodeId]) -> Diagnostic {
        let span = certain_homes
            .iter()
            .skip(1)
            .find_map(|code_id| match self.code.get(*code_id) {
                CodeState::Indexed { source } => function_form_span(source, function_ref),
                _ => None,
            })
            .or_else(|| {
                certain_homes.iter().find_map(|code_id| match self.code.get(*code_id) {
                    CodeState::Indexed { source } => function_form_span(source, function_ref),
                    _ => None,
                })
            })
            .unwrap_or(Span::DUMMY);
        Diagnostic::error(
            codes::RESOLVE_DUPLICATE_FUNCTION,
            format!("`{}/{}` is already defined", function_ref.name, function_ref.arity),
            span,
        )
    }
}

impl<T: Telemetry> ExecutionContext<'_, T> {
    pub(crate) fn emit_world_key<K: Any>(&self, name: &'static [&'static str], key: &K) {
        self.telemetry.raw_event2(name, &*self.world, key);
    }

    fn emit_generated_function_defined(&self, function: &FunctionId, owner: &FunctionId) {
        self.telemetry.raw_event3(
            &["fz", "compiler2", "function", "defined"],
            &*self.world,
            function,
            owner,
        );
    }

    pub fn submit_code(&mut self, name: Option<String>, text: String) -> CodeId {
        let code_id = self.world.submit_code(name, text);
        emit_code_submitted(self.telemetry, self.world, &code_id);
        code_id
    }

    pub fn submit_root(
        &mut self,
        module_name: Option<String>,
        name: String,
        arity: usize,
        need: ExecutableNeed,
    ) -> RootId {
        let root_id = self.world.submit_root(module_name, name, arity, need);
        self.emit_world_key(&["fz", "compiler2", "root", "submitted"], &root_id);
        root_id
    }

    pub(crate) fn emit_unresolved_diagnostics(&mut self, waits: &[UnresolvedWait<Job, FactKey>]) {
        let diagnostics = self.world.take_unresolved_diagnostics(waits);
        if !diagnostics.is_empty() {
            emit_through(self.telemetry, &diagnostics);
        }
    }

    pub(crate) fn emit_warning_once(&mut self, diagnostic: Diagnostic) {
        if diagnostic.severity != Severity::Warning {
            emit_through(self.telemetry, std::slice::from_ref(&diagnostic));
            return;
        }
        self.world.note_warning_once(diagnostic);
    }

    pub(crate) fn flush_reported_warnings(&mut self) {
        let diagnostics = self.world.take_reported_warnings();
        if !diagnostics.is_empty() {
            emit_through(self.telemetry, &diagnostics);
        }
    }

    pub fn define_activation_analysis(&mut self, key: &ActivationKey, analysis: ActivationAnalysis) -> bool {
        // value_types are already in the activation's addressed frame: params bind
        // to the addressed key inputs (`analyze_activation`), so a value at param i
        // carries address a{i}. No re-canonicalization — the old per-type encounter
        // pass (alpha_normalize_vars) re-numbered them into a frame that DIVERGED
        // from the key (fz-hwn.27.8); addressing at the binder is the canonical form.
        let changed = self.world.define_activation_analysis(key, analysis);
        if changed {
            self.emit_world_key(&["fz", "compiler2", "activation_analysis", "defined"], key);
        }
        changed
    }

    pub fn define_activation_return(&mut self, key: &ActivationKey, evidence: Option<Ty>) -> bool {
        // Return evidence is produced in the activation's addressed frame (clause
        // returns over addressed inputs), so it is already canonical — the old
        // encounter-order pass diverged it from the key (fz-hwn.27.8).
        // The publisher of a ReturnType claim is, by construction, the
        // activation's own analysis job — its rebase state selects join
        // (the within-epoch ascent) or replace (the narrowing path).
        let outcome = self.world.define_activation_return_outcome(key, evidence);
        if outcome.changed {
            self.emit_world_key(&["fz", "compiler2", "return_type", "defined"], key);
        }
        if outcome.widened {
            self.emit_world_key(&["fz", "compiler2", "return_type", "widened"], key);
        }
        outcome.changed
    }

    pub fn define_callsite_summary(&mut self, key: CallSiteKey, summary: CallSiteSummary) -> bool {
        let changed = self.world.define_callsite_summary(key.clone(), summary);
        if changed {
            self.emit_world_key(&["fz", "compiler2", "callsite", "defined"], &key);
        }
        changed
    }

    pub(crate) fn define_backend_program(&mut self, root: RootId, program: BackendProgram) -> bool {
        let changed = self.world.define_backend_program(root, program);
        if changed {
            self.emit_world_key(&["fz", "compiler2", "backend_program", "defined"], &root);
        }
        changed
    }

    pub(crate) fn define_macro_executable(
        &mut self,
        function: FunctionId,
        root: RootId,
        backend_revision: u64,
        program: BackendProgram,
    ) -> bool {
        let changed = self
            .world
            .define_macro_executable(function, root, backend_revision, program);
        if changed {
            self.emit_world_key(&["fz", "compiler2", "macro_executable", "defined"], &function);
        }
        changed
    }

    pub(crate) fn run_macro_on_source(
        &mut self,
        function: FunctionId,
        source: &QuotedSourceRoot,
        caller: AnyValueRef,
        args: &[AnyValueRef],
    ) -> Result<QuotedSourceRoot, String> {
        self.world.run_macro_on_source_with(
            function,
            source,
            caller,
            args,
            |types, transport, program, process, args| {
                crate::ir_interp::run_backend_entry_on_process(
                    types,
                    transport,
                    self.telemetry,
                    &fz_runtime::output::STDOUT_OUTPUT,
                    program,
                    process,
                    args,
                )
            },
        )
    }

    pub(crate) fn define_native_program(&mut self, root: RootId, program: NativeProgram) -> bool {
        let changed = self.world.define_native_program(root, program);
        if changed {
            self.emit_world_key(&["fz", "compiler2", "native_program", "defined"], &root);
        }
        changed
    }

    pub fn define_module(&mut self, id: ModuleId, base: Namespace, interface: ModuleInterface) -> bool {
        let changed = self.world.define_module(id, base, interface);
        if changed {
            self.emit_world_key(&["fz", "compiler2", "module", "defined"], &id);
        }
        changed
    }

    pub(crate) fn validate_module_interface_expectations(
        &self,
        id: ModuleId,
        interface: &ModuleInterface,
    ) -> Result<(), FatalError> {
        if let Some(diagnostic) = self.world.module_interface_diagnostic(id, interface) {
            return Err(emit_job_diagnostic(self.telemetry, diagnostic));
        }
        Ok(())
    }

    pub fn note_type_decl(&mut self, name: &TypeName, decl: NotedTypeDecl) {
        if self.world.note_type_decl(name, decl) {
            self.emit_world_key(&["fz", "compiler2", "type", "noted"], name);
        }
    }

    pub(crate) fn record_function_type_refs(&mut self, function: &FunctionId, refs: Vec<TypeName>) {
        if self.world.record_function_type_refs(function, refs) {
            self.emit_world_key(
                &["fz", "compiler2", "type", "references", "function", "recorded"],
                function,
            );
        }
    }

    pub(crate) fn record_type_def_refs(&mut self, name: &TypeName, refs: Vec<TypeName>) {
        if self.world.record_type_def_refs(name, refs) {
            self.emit_world_key(&["fz", "compiler2", "type", "references", "type", "recorded"], name);
        }
    }

    pub(crate) fn define_type_def(&mut self, name: &TypeName, def: TypeDef) -> bool {
        let changed = self.world.define_type_def(name, def);
        if changed {
            self.emit_world_key(&["fz", "compiler2", "type", "defined"], name);
        }
        changed
    }

    pub(crate) fn define_struct_def(&mut self, module: ModuleId, def: StructDef) -> bool {
        let changed = self.world.define_struct_def(module, def);
        if changed {
            self.emit_world_key(&["fz", "compiler2", "struct_def", "defined"], &module);
        }
        changed
    }

    pub(crate) fn note_struct_field_expectation(
        &mut self,
        module: ModuleId,
        field: String,
        requester: InterfaceRequester,
    ) -> Result<(), FatalError> {
        self.world.note_struct_field_expectation(module, field, requester);
        if self.world.struct_def(module).is_some() {
            self.validate_struct_field_expectations(module)?;
        }
        Ok(())
    }

    pub(crate) fn validate_struct_field_expectations(&self, module: ModuleId) -> Result<(), FatalError> {
        let diagnostics = self.world.struct_field_diagnostics(module);
        if diagnostics.is_empty() {
            Ok(())
        } else {
            emit_through(self.telemetry, &diagnostics);
            Err(FatalError)
        }
    }

    pub(crate) fn refresh_protocol_dispatch(&mut self, protocol: ModuleId) -> bool {
        let changed = self.world.refresh_protocol_dispatch(protocol);
        if changed {
            self.emit_world_key(&["fz", "compiler2", "protocol_dispatch", "defined"], &protocol);
        }
        changed
    }

    pub(crate) fn define_function(
        &mut self,
        id: FunctionId,
        source: FunctionSource,
        expanded_source: FunctionSource,
        surface: FunctionSurface,
    ) -> bool {
        let changed = self.world.define_function(id, source, expanded_source, surface);
        if changed {
            self.emit_world_key(&["fz", "compiler2", "function", "defined"], &id);
        }
        changed
    }

    pub(crate) fn stash_function_source(&mut self, function: FunctionId, source: FunctionSource) -> bool {
        let changed = self.world.stash_function_source(function, source);
        if changed {
            self.emit_world_key(&["fz", "compiler2", "function", "source", "stashed"], &function);
        }
        changed
    }

    pub(crate) fn publish_pending_function_source(&mut self, function: FunctionId) -> Option<bool> {
        self.world.pending_function_source(function)?;
        let changed = self.world.publish_pending_function_source(function)?;
        if changed {
            self.emit_function_source_noted(function);
        }
        Some(changed)
    }

    fn emit_function_source_noted(&self, function: FunctionId) {
        self.emit_world_key(&["fz", "compiler2", "function", "source", "noted"], &function);
    }

    pub(crate) fn note_expanded_function_source(&mut self, function: FunctionId, source: FunctionSource) -> bool {
        let changed = self.world.note_expanded_function_source(function, source);
        if changed {
            self.emit_world_key(&["fz", "compiler2", "function", "source", "expanded"], &function);
        }
        changed
    }

    pub(crate) fn define_function_contract(&mut self, function: FunctionId, contract: FunctionContract) -> bool {
        let changed = self.world.define_function_contract(function, contract);
        if changed {
            self.emit_world_key(&["fz", "compiler2", "function_contract", "defined"], &function);
        }
        changed
    }

    pub(crate) fn define_protocol_callback(&mut self, function: &FunctionId, protocol: &ModuleId) {
        self.world.define_protocol_callback(function, protocol);
        self.telemetry.raw_event3(
            &["fz", "compiler2", "protocol_callback", "defined"],
            &*self.world,
            function,
            protocol,
        );
    }

    pub(crate) fn define_protocol_impl(
        &mut self,
        protocol: &ModuleId,
        target: &ModuleId,
        callbacks: HashMap<FunctionId, ProtocolCallbackImpl>,
    ) {
        self.world.define_protocol_impl(protocol, target, callbacks);
        self.telemetry.raw_event3(
            &["fz", "compiler2", "protocol_impl", "defined"],
            &*self.world,
            protocol,
            target,
        );
    }

    pub(crate) fn define_generated_function(
        &mut self,
        owner: FunctionId,
        namespace: Namespace,
        capture_params: Vec<String>,
        surface: FunctionSurface,
    ) -> (FunctionId, bool) {
        let (id, changed) = self
            .world
            .define_generated_function(owner, namespace, capture_params, surface);
        if changed {
            self.emit_generated_function_defined(&id, &owner);
        }
        (id, changed)
    }

    pub(crate) fn define_lowered_body(&mut self, function: FunctionId, body: LoweredBody) -> bool {
        let changed = self.world.define_lowered_body(function, body);
        if changed {
            self.emit_world_key(&["fz", "compiler2", "lowered_body", "defined"], &function);
        }
        changed
    }

    pub(crate) fn define_guard_dispatch(&mut self, function: FunctionId, dispatch: PatternGuardDispatch<Ty>) -> bool {
        let changed = self.world.define_guard_dispatch(function, dispatch);
        if changed {
            self.emit_world_key(&["fz", "compiler2", "guard_dispatch", "defined"], &function);
        }
        changed
    }

    pub(crate) fn define_entry_dispatch(&mut self, function: FunctionId, plan: PatternDispatchPlan<Ty>) -> bool {
        let changed = self.world.define_entry_dispatch(function, plan);
        if changed {
            self.emit_world_key(&["fz", "compiler2", "entry_dispatch", "defined"], &function);
        }
        changed
    }

    pub(crate) fn demand_function_scope(&mut self, function: FunctionId) -> Result<Vec<FactKey>, FatalError> {
        self.world
            .demand_function_scope(function)
            .map_err(|diagnostic| emit_job_diagnostic(self.telemetry, *diagnostic))
    }

    pub(crate) fn wait_for_type_decl(&mut self, module: ModuleId) -> JobEffects {
        let (effects, registration) = self.world.wait_for_type_decl_registration(module);
        if let Some(registration) = registration {
            self.emit_runtime_module_registration(&registration);
        }
        effects
    }

    pub(crate) fn ensure_runtime_module(&mut self, module: ModuleId) -> Option<CodeId> {
        let registration = self.world.ensure_runtime_module_registration(module)?;
        self.emit_runtime_module_registration(&registration);
        Some(registration.code_id)
    }

    fn emit_runtime_module_registration(&self, registration: &RuntimeModuleRegistration) {
        if registration.inserted {
            self.telemetry.raw_event2(
                &["fz", "compiler2", "code", "submitted"],
                &*self.world,
                &registration.code_id,
            );
        }
    }
}

fn emit_code_submitted(tel: &impl Telemetry, world: &World, code: &CodeId) {
    tel.raw_event2(&["fz", "compiler2", "code", "submitted"], world, code);
}
