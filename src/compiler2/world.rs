//! Compiler2's owned world state.
//!
//! Compiler-owned identities are total here. A `CodeId`, `ModuleId`,
//! `FunctionId`, or `RootId` that came from Compiler2 must resolve; a bad id is
//! a bug and should panic at the lookup boundary. `Option` is reserved for
//! legitimate state absence like "this known function is still a placeholder"
//! or "this known code has not been indexed yet".

use std::cmp::Reverse;
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::diag::diagnostic::Severity;
use crate::diag::driver::emit_through;
use crate::diag::{Diagnostic, codes};
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardDispatch};
use crate::modules::identity::{Mfa, ModuleName};
use crate::modules::runtime_library;
use crate::source::Span;
use crate::telemetry::{Telemetry, opaque, opaque_debug};
use crate::{FunctionSurface, measurements, metadata};

use super::CodeId;
use super::artifact::{
    BackendProgram, BackendProgramMap, MacroExecutable, MacroExecutableMap, NativeProgram, NativeProgramMap,
};
use super::body::{LoweredBody, LoweredBodyMap};
use super::code::{CodeMap, CodeState, QuotedCodeSource};
use super::contract::{FunctionContract, FunctionContractMap};
use super::deps::UnresolvedWait;
use super::dispatch::{EntryDispatchMap, GuardDispatchMap};
use super::drive::{FactKey, Job, JobEffects, WorkGraph};
use super::identity::{
    ActivationKey, ExecutableKey, ExecutableNeed, ExpandedFunctionSourceMap, FunctionId, FunctionMap, FunctionRef,
    FunctionSource, ModuleId, ModuleMap, ModuleSourceKind, ModuleState, NotedTypeDecl, PendingFunctionSourceMap,
    RootEntry, RootId, RootKind, RootMap, TypeDeclMap, TypeName, TypeRefMap,
};
use super::keying::{DispatchDemand, DispatchMaskMap, RecursiveMap};
use super::module_interface::{InterfaceCallableKind, InterfaceExpectation, InterfaceRequester, ModuleInterface};
use super::namespace::{Namespace, NamespaceStore, NamespaceSymbol};
use super::protocol::{
    ProtocolCallback, ProtocolCallbackImpl, ProtocolCallbackMap, ProtocolDispatch, ProtocolDispatchArm,
    ProtocolDispatchMap, ProtocolImpl, ProtocolImplKey, ProtocolImplMap, ProtocolImplProviderMap, protocol_domain_tag,
};
use super::quoted_surface::{ReservedSourceDefinition, ScopeForm, reserved_source_definition};
use super::runtime::{self, RuntimeModuleCode};
use super::scheduler::{FatalError, WorkStartReason, WorkStartTally};
use super::scope::ScopeSnapshot;
use super::semantic::{
    ActivationAnalysis, ActivationInputMap, ActivationMap, CallSiteKey, CallSiteMap, CallSiteSummary, CallSiteTargets,
    CallSiteTargetsMap, ContributionReplace,
};
use super::source::{
    QuotedLexicalContext, QuotedLexicalContextKind, QuotedSourceBuilder, QuotedSourceError, QuotedSourceMetadata,
    QuotedSourceRoot,
};
use super::structdef::{StructDef, StructDefMap, StructExpectationMap, StructFieldExpectation};
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

pub struct World<'a> {
    tel: &'a dyn Telemetry,
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
    function_contracts: FunctionContractMap,
    bodies: LoweredBodyMap,
    guard_dispatches: GuardDispatchMap,
    entry_dispatches: EntryDispatchMap,
    recursive: RecursiveMap,
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
}

impl std::fmt::Debug for World<'_> {
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

impl<'a> World<'a> {
    pub fn new(tel: &'a dyn Telemetry) -> Self {
        let mut world = Self {
            tel,
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
            function_contracts: FunctionContractMap::new(),
            bodies: LoweredBodyMap::new(),
            guard_dispatches: GuardDispatchMap::new(),
            entry_dispatches: EntryDispatchMap::new(),
            recursive: RecursiveMap::new(),
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
        };
        world.runtime_modules = runtime::bootstrap(&mut world.modules);
        world.runtime_prelude = world.code.define(
            Some("runtime:runtime.fz".to_string()),
            runtime_library::prelude_source().to_string(),
        );
        world
    }

    pub fn tel(&self) -> &'a dyn Telemetry {
        self.tel
    }

    pub fn root_function(&self, root: RootId) -> FunctionId {
        self.roots.get(root).function
    }

    pub(crate) fn types(&self) -> &Types {
        &self.types
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
    fn register_code(&mut self, name: Option<String>, text: String) -> CodeId {
        let bytes = text.len();
        let code_id = self.code.define(name, text);
        self.tel.execute(
            &["fz", "compiler2", "code", "submitted"],
            &measurements! {
                code_id: code_id.as_u32(),
                bytes: bytes,
            },
            &metadata! {},
        );
        code_id
    }

    pub fn submit_code(&mut self, name: Option<String>, text: String) -> CodeId {
        let code_id = self.register_code(name, text);
        // External front door: the submitted code does not exist to be
        // waited on before this call creates it, matching `submit_root`'s
        // `SeedRoot` ignition below. This is the ONE place an `IndexCode`/
        // `ScopeCode` work-start is a genuine external ignition; every internal
        // (mid-job) runtime-module mint leaves the code to be pulled instead.
        self.work_graph
            .enqueue(Job::IndexCode(code_id), WorkStartReason::Ignition);
        if !self.roots.is_empty() {
            self.work_graph
                .enqueue(Job::ScopeCode(code_id), WorkStartReason::Ignition);
        }
        code_id
    }

    pub fn submit_module_interface(&mut self, module_name: String, interface: ModuleInterface) -> ModuleId {
        let module = self.reference_module(module_name);
        self.define_module_interface(module, interface);
        // External front door: the same ignition shape as `submit_code`/`submit_root`.
        self.work_graph
            .enqueue(Job::DefineModuleInterface(module), WorkStartReason::Ignition);
        module
    }

    pub fn submit_root(
        &mut self,
        module_name: Option<String>,
        name: String,
        arity: usize,
        need: ExecutableNeed,
    ) -> RootId {
        let module = match module_name.as_deref() {
            Some(name) => self.reference_module(name.to_string()),
            None => ModuleId::GLOBAL,
        };
        let function = self.reference_function(module, name, arity);
        // The root is the program's public entry: its inputs arrive from
        // outside the analyzed world, so `any` is earned here — the same
        // boundary rule macro roots already follow. An arity-N root must
        // carry N slots of evidence; absence would starve its clauses.
        let any = self.types.any();
        let root_id = self.roots.define(RootEntry {
            function,
            input: vec![any; arity],
            need,
            kind: RootKind::Runtime,
        });
        // The external ignition point: the root does not exist to be waited
        // on before this call creates it. Everything downstream is pulled --
        // the root's entry analysis via `demand_root_entry_analyses`, every
        // other producer via the fact->producer map.
        self.work_graph
            .enqueue(Job::SeedRoot(root_id), WorkStartReason::Ignition);
        let root = self.roots.get(root_id);
        let function_ref = self.functions.reference_for(function);
        self.tel.execute(
            &["fz", "compiler2", "root", "submitted"],
            &measurements! {
                root_id: root_id.as_u32(),
                module_id: module.as_u32(),
                function_id: function.as_u32(),
                arity: arity,
                pending_codes: self.code.len(),
            },
            &metadata! {
                root: opaque_debug(root),
                function_ref: opaque_debug(function_ref),
            },
        );
        root_id
    }

    pub(crate) fn complete_job(&mut self, job: Job, effects: JobEffects) -> super::AppliedStep<Job, FactKey> {
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
        for activation in &activation_input_changed {
            if let Some(inputs) = self.activation_inputs.get(activation) {
                self.tel.execute(
                    &["fz", "compiler2", "activation_inputs", "defined"],
                    &measurements! {
                        root_id: activation.root.as_u32(),
                        function_id: activation.function.as_u32(),
                        input_arity: inputs.len(),
                        rebased: rebased,
                    },
                    &metadata! {
                        activation: opaque_debug(activation),
                        inputs: opaque_debug(inputs),
                        inputs_display: opaque_debug(&inputs.iter().map(|ty| self.types.display(ty)).collect::<Vec<_>>()),
                        publisher: opaque_debug(&job),
                    },
                );
            }
        }
        let mut outputs = effects.outputs;
        outputs.extend(activation_input_outputs.into_iter().map(FactKey::ActivationInputs));
        let outputs = dedupe_job_facts(outputs);
        let mut changed = effects.changed;
        changed.extend(activation_input_changed.into_iter().map(FactKey::ActivationInputs));
        let changed = dedupe_job_facts(changed);
        // Captured before `outputs` moves into `complete`: the two record
        // sites that keep `activation_frontier` in lockstep with the fact
        // table, mirrored on the publish/settle pair the way
        // `insert_transport_shape`/`remove_transport_shape` keep their own
        // by-symbol index coherent.
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
        self.tel.event(
            &["fz", "compiler2", "work_graph", "applied"],
            metadata! {
                job: opaque_debug(&job),
                step: opaque_debug(&step),
            },
        );
        step
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

    pub(crate) fn emit_unresolved_diagnostics(&mut self, waits: &[UnresolvedWait<Job, FactKey>]) {
        let issues = self.unresolved_issues(waits);
        let next = issues.iter().map(|issue| issue.key).collect::<HashSet<_>>();
        let diagnostics = issues
            .into_iter()
            .filter(|issue| !self.reported_unresolved.contains(&issue.key))
            .map(|issue| issue.diagnostic)
            .collect::<Vec<_>>();
        if !diagnostics.is_empty() {
            emit_through(self.tel, &diagnostics);
        }
        self.reported_unresolved = next;
    }

    pub(crate) fn emit_warning_once(&mut self, diagnostic: Diagnostic) {
        if diagnostic.severity != Severity::Warning {
            emit_through(self.tel, std::slice::from_ref(&diagnostic));
            return;
        }
        if self
            .reported_warnings
            .insert(WarningDiagnosticKey::from_diagnostic(&diagnostic))
        {
            self.warning_diagnostics.push(diagnostic);
        }
    }

    pub(crate) fn flush_reported_warnings(&mut self) {
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
        if !self.warning_diagnostics.is_empty() {
            emit_through(self.tel, &self.warning_diagnostics);
        }
        self.warning_diagnostics.clear();
    }

    pub(crate) fn clear_unresolved_diagnostics(&mut self) {
        self.reported_unresolved.clear();
    }

    pub(crate) fn clear_reported_warnings(&mut self) {
        self.reported_warnings.clear();
        self.warning_diagnostics.clear();
    }

    pub fn code_name(&self, id: CodeId) -> Option<&str> {
        self.code.name(id)
    }

    pub fn code_text(&self, id: CodeId) -> &str {
        self.code.text(id)
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

    /// The canonical inputs of an activation, once its fact exists. The key
    /// itself carries the canonical (alpha-normalized) inputs — the fact only
    /// records that the activation has been demanded. Body input evidence lives
    /// in the separate `ActivationInputs(key)` fact.
    pub(crate) fn activation_inputs(&self, key: &ActivationKey) -> Option<Vec<Ty>> {
        self.fact_revision(&FactKey::ActivationInputs(key.clone()))?;
        Some(self.activation_inputs.get(key)?.clone())
    }

    pub fn activation_analysis(&self, key: &ActivationKey) -> Option<&ActivationAnalysis> {
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

    pub fn define_activation_analysis(&mut self, key: &ActivationKey, analysis: ActivationAnalysis) -> bool {
        // value_types are already in the activation's addressed frame: params bind
        // to the addressed key inputs (`analyze_activation`), so a value at param i
        // carries address a{i}. No re-canonicalization — the old per-type encounter
        // pass (alpha_normalize_vars) re-numbered them into a frame that DIVERGED
        // from the key (fz-hwn.27.8); addressing at the binder is the canonical form.
        let changed = self.activations.define_analysis(key, analysis);
        let analysis = self
            .activations
            .get(key)
            .and_then(|slot| slot.analysis())
            .expect("activation analysis should be readable right after it is defined");
        self.tel.execute(
            &["fz", "compiler2", "activation_analysis", "defined"],
            &measurements! {
                root_id: key.root.as_u32(),
                function_id: key.function.as_u32(),
                reachable_clauses: analysis.reachable_clauses.len(),
                callsites: analysis.callsites.len(),
                values: analysis.value_types.len(),
            },
            &metadata! {
                activation: opaque_debug(key),
                analysis: opaque_debug(analysis),
            },
        );
        changed
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
    ) -> HashMap<ActivationKey, Vec<Ty>> {
        let mut next = HashMap::<ActivationKey, Vec<Ty>>::new();
        for (activation, inputs) in contributions {
            // Canonicalize the input evidence the same whole-scope way the key is
            // built (fz-hwn.27.6, A): one shared addressing pass, so distinct
            // observed vars stay distinct and the evidence shares the key's
            // canonical form. Idempotent on already-addressed contributions.
            let normalized = self.types.address_inputs(&inputs);
            let normalized = if self.recursive.get(activation.function).copied().unwrap_or(false) {
                let mask = self
                    .dispatch_masks
                    .get(activation.function)
                    .cloned()
                    .unwrap_or_else(|| vec![DispatchDemand::Whole; normalized.len()]);
                self.types.convergence_collapse_evidence_inputs(&normalized, &mask)
            } else {
                normalized
            };
            match next.entry(activation) {
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(normalized);
                }
                std::collections::hash_map::Entry::Occupied(mut entry) => {
                    let current = entry.get_mut();
                    assert_eq!(
                        current.len(),
                        normalized.len(),
                        "one activation input fact cannot receive differing arities from one publisher",
                    );
                    for (current_input, next_input) in current.iter_mut().zip(normalized) {
                        *current_input =
                            if *current_input == next_input || self.types.is_equivalent(current_input, &next_input) {
                                *current_input
                            } else {
                                self.types.union(*current_input, next_input)
                            };
                    }
                }
            }
        }
        next
    }

    pub fn define_activation_return(&mut self, key: &ActivationKey, evidence: Option<Ty>) -> bool {
        // Return evidence is produced in the activation's addressed frame (clause
        // returns over addressed inputs), so it is already canonical — the old
        // encounter-order pass diverged it from the key (fz-hwn.27.8).
        // The publisher of a ReturnType claim is, by construction, the
        // activation's own analysis job — its rebase state selects join
        // (the within-epoch ascent) or replace (the narrowing path).
        let rebased = self.work_graph.rebased(&Job::AnalyzeActivation(key.clone()));
        let outcome = self.activations.define_return(&mut self.types, key, evidence, rebased);
        let evidence = self.activations.get(key).and_then(|slot| slot.return_ty().copied());
        self.tel.execute(
            &["fz", "compiler2", "return_type", "defined"],
            &measurements! {
                root_id: key.root.as_u32(),
                function_id: key.function.as_u32(),
                ascents: outcome.ascents,
                rebased: rebased,
                changed: outcome.changed as u64,
            },
            &metadata! {
                activation: opaque_debug(key),
                return_ty: opaque_debug(&evidence),
            },
        );
        if outcome.widened {
            self.tel.execute(
                &["fz", "compiler2", "return_type", "widened"],
                &measurements! {
                    root_id: key.root.as_u32(),
                    function_id: key.function.as_u32(),
                    ascents: outcome.ascents,
                },
                &metadata! {
                    activation: opaque_debug(key),
                },
            );
        }
        outcome.changed
    }

    pub fn define_callsite_summary(&mut self, key: CallSiteKey, mut summary: CallSiteSummary) -> bool {
        for target in &mut summary.targets {
            // Whole-scope addressing, matching the key and surfaces (fz-hwn.27.6,
            // A): one shared pass over the surface inputs, not per-position.
            target.surface_inputs = self.types.address_inputs(&target.surface_inputs);
            // The embedded activation key is already canonical: its sole producer
            // (`prepare_function_call` → `canonical_activation_key` → `from_inputs`)
            // mints through the single addressing pass, so re-addressing it here was
            // a no-op left over from the conflation engine deleted in fz-hwn.27.6.
            // return_ty is already in the activation's addressed frame, matching the
            // surfaces addressed just above — no encounter re-normalization (fz-hwn.27.8).
        }
        let changed = self.callsites.define(&mut self.types, key.clone(), summary);
        let summary = self
            .callsites
            .get(&key)
            .expect("callsite summaries should be readable right after they are defined");
        self.tel.execute(
            &["fz", "compiler2", "callsite", "defined"],
            &measurements! {
                root_id: key.activation.root.as_u32(),
                function_id: key.activation.function.as_u32(),
                callsite_id: key.callsite.as_u32(),
                input_arity: summary.arity(),
                target_count: summary.targets.len(),
                changed: changed as u64,
            },
            &metadata! {
                callsite: opaque_debug(&key),
                summary: opaque_debug(summary),
            },
        );
        changed
    }

    pub fn callsite_summary(&self, key: &CallSiteKey) -> Option<&CallSiteSummary> {
        self.callsites.get(key)
    }

    pub fn define_callsite_targets(&mut self, key: CallSiteKey, targets: CallSiteTargets) -> bool {
        self.callsite_targets.define(key, targets)
    }

    pub fn callsite_targets(&self, key: &CallSiteKey) -> Option<&CallSiteTargets> {
        self.callsite_targets.get(key)
    }

    pub(crate) fn define_backend_program(&mut self, root: RootId, program: BackendProgram) -> bool {
        let changed = self.backend.define(root, program);
        let program = self
            .backend
            .get(root)
            .expect("backend programs should be readable right after they are defined");
        self.tel.execute(
            &["fz", "compiler2", "backend_program", "defined"],
            &measurements! {
                root_id: root.as_u32(),
                atom_count: program.atom_names.len(),
                executable_count: program.executables.len(),
                callable_entry_count: program.callable_entries.len(),
                changed: changed as u64,
            },
            &metadata! {
                program: opaque_debug(program),
                root_id: opaque_debug(&root),
            },
        );
        changed
    }

    pub(crate) fn backend_program(&self, root: RootId) -> BackendProgram {
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

    pub(crate) fn define_macro_executable(
        &mut self,
        function: FunctionId,
        root: RootId,
        backend_revision: u64,
        program: BackendProgram,
    ) -> bool {
        let changed = self.macro_executables.define(
            function,
            MacroExecutable {
                root,
                backend_revision,
                program,
            },
        );
        let program = &self
            .macro_executables
            .get(function)
            .expect("macro executables should be readable right after they are defined")
            .program;
        self.tel.execute(
            &["fz", "compiler2", "macro_executable", "defined"],
            &measurements! {
                function_id: function.as_u32() as u64,
                root_id: root.as_u32() as u64,
                backend_revision: backend_revision,
                executable_count: program.executables.len() as u64,
                changed: changed as u64,
            },
            &metadata! {
                program: opaque_debug(program),
            },
        );
        changed
    }

    pub(crate) fn macro_executable(&self, function: FunctionId) -> Option<&MacroExecutable> {
        self.macro_executables.get(function)
    }

    pub(crate) fn run_macro_on_source(
        &mut self,
        function: FunctionId,
        source: &QuotedSourceRoot,
        caller: AnyValueRef,
        args: &[AnyValueRef],
    ) -> Result<QuotedSourceRoot, String> {
        let executable = self
            .macro_executable(function)
            .ok_or_else(|| format!("macro {} is not executable", function.as_u32()))?
            .clone();
        // Inputs by semantic role: __CALLER__ first, then the user args. The
        // executable's lane layout — not a fixed ABI — decides what is actually
        // passed, so a __CALLER__ the macro body never uses is elided like any
        // other unused input, keeping the macro caller lane-consistent with the
        // executable the same way a generated caller is.
        let mut semantic_values = Vec::with_capacity(1 + args.len());
        semantic_values.push(RuntimeValue::Ref(caller));
        semantic_values.extend(args.iter().copied().map(RuntimeValue::Ref));
        let runtime_args =
            crate::ir_interp::encode_macro_entry_inputs(&executable.program, &self.transport, &semantic_values)?;
        let value = source.lend_process(|process| {
            crate::ir_interp::run_backend_entry_on_process(
                &mut self.types,
                &self.transport,
                self.tel,
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

    pub(crate) fn define_native_program(&mut self, root: RootId, program: NativeProgram) -> bool {
        let changed = self.native.define(root, program);
        let program = self
            .native
            .get(root)
            .expect("native programs should be readable right after they are defined");
        self.tel.execute(
            &["fz", "compiler2", "native_program", "defined"],
            &measurements! {
                root_id: root.as_u32(),
                body_count: program.bodies.len(),
                callable_boundary_count: program.callable_boundaries.len(),
                fn_count: program.module.fns.len(),
                changed: changed as u64,
            },
            &metadata! {
                program: opaque_debug(program),
                root_id: opaque_debug(&root),
            },
        );
        changed
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

    pub fn reference_child_module(&mut self, parent: ModuleId, local_name: &str) -> ModuleId {
        let name = self.qualified_module_name(parent, local_name);
        self.modules.reference_named(name)
    }

    pub fn define_module(&mut self, id: ModuleId, base: Namespace, interface: ModuleInterface) -> bool {
        let code = self.module_definition_code(id);
        let changed = self.modules.define(id, code, base, interface);
        let module = self.modules.get(id);
        self.tel.execute(
            &["fz", "compiler2", "module", "defined"],
            &measurements! {
                code_id: code.as_u32(),
                module_id: id.as_u32(),
            },
            &metadata! {
                module: opaque_debug(module),
                module_id: opaque_debug(&id),
            },
        );
        changed
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

    pub(crate) fn validate_module_interface_expectations(
        &self,
        id: ModuleId,
        interface: &ModuleInterface,
    ) -> Result<(), FatalError> {
        for expectation in interface.expectations() {
            if interface
                .callables()
                .iter()
                .any(|callable| expectation.matches_callable(callable))
            {
                continue;
            }
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
            return Err(emit_job_diagnostic(
                self,
                Diagnostic::error(
                    codes::RESOLVE_UNKNOWN_IMPORT,
                    message,
                    expectation
                        .requester
                        .as_ref()
                        .map(|requester| requester.span)
                        .unwrap_or(Span::DUMMY),
                ),
            ));
        }
        Ok(())
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
    pub fn note_type_decl(&mut self, name: TypeName, decl: NotedTypeDecl) {
        if self.type_decls.note(name.clone(), decl) {
            let decl = self
                .type_decls
                .get(&name)
                .expect("type decls should be readable right after they are noted");
            self.tel.execute(
                &["fz", "compiler2", "type", "noted"],
                &measurements! {
                    module_id: name.module.as_u32(),
                    arity: name.arity,
                    namespace: decl.namespace.as_u32(),
                },
                &metadata! {
                    name: &name.name,
                    decl: opaque_debug(decl),
                },
            );
        }
    }

    pub fn type_decl(&self, name: &TypeName) -> Option<&NotedTypeDecl> {
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
    pub(crate) fn record_function_type_refs(&mut self, function: FunctionId, mut refs: Vec<TypeName>) {
        dedup_type_names(&mut refs);
        if self.type_refs.record_function(function, refs) {
            let consumer_name = &self.functions.reference_for(function).name;
            for referenced in self.type_refs.function_refs(function) {
                self.emit_type_referenced("fn", consumer_name, referenced);
            }
        }
    }

    // Consumed by the contract re-seat (fz-rh2.12.4); recorded one inch ahead.
    pub(crate) fn function_type_refs(&self, function: FunctionId) -> &[TypeName] {
        self.type_refs.function_refs(function)
    }

    /// Records the type names a `@type` body references — the wait-set
    /// `DeriveTypeDef` resolves against before minting the symbol (fz-rh2.12.2).
    pub(crate) fn record_type_def_refs(&mut self, name: TypeName, mut refs: Vec<TypeName>) {
        dedup_type_names(&mut refs);
        if self.type_refs.record_type(name.clone(), refs) {
            for referenced in self.type_refs.type_refs(&name) {
                self.emit_type_referenced("type", &name.name, referenced);
            }
        }
    }

    /// The type names a `@type` body references — `DeriveTypeDef`'s wait-set.
    pub(crate) fn type_def_refs(&self, name: &TypeName) -> &[TypeName] {
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
    pub(crate) fn define_type_def(&mut self, name: TypeName, def: TypeDef) -> bool {
        let changed = self.type_defs.define(name.clone(), def);
        let def = self
            .type_defs
            .get(&name)
            .expect("type defs should be readable right after they are defined");
        self.tel.execute(
            &["fz", "compiler2", "type", "defined"],
            &measurements! {
                module_id: name.module.as_u32(),
                arity: name.arity,
                params: def.params.len(),
                changed: changed as u64,
            },
            &metadata! {
                name: &name.name,
                def: opaque_debug(def),
                types: opaque(&self.types),
            },
        );
        changed
    }

    pub(crate) fn type_def(&self, name: &TypeName) -> Option<&TypeDef> {
        self.type_defs.get(name)
    }

    /// Reads `module`'s resolved `defstruct`, if `StructDefined(module)` has
    /// published one. This is the fact-backed replacement for scanning
    /// `ModuleState` source for a `defstruct` form — the protocol-impl-target
    /// classification and `struct_assertion_ty` read schemas through here.
    pub(crate) fn struct_def(&self, module: ModuleId) -> Option<&StructDef> {
        self.struct_defs.get(module)
    }

    /// Publishes a resolved `defstruct` under `module` and emits the
    /// callee-tier `struct_def defined` signal, mirroring `define_type_def`.
    /// `resolve.rs`'s `TypeExpr::StructRecord` path (via `struct_def_fields`),
    /// the protocol-impl-target classification, and `struct_assertion_ty` read
    /// this store; `module_struct_fields`'s source scan below remains the reader
    /// for the struct-literal/pattern lowering and backend consumers not yet
    /// migrated.
    pub(crate) fn define_struct_def(&mut self, module: ModuleId, def: StructDef) -> bool {
        let changed = self.struct_defs.define(module, def);
        let def = self
            .struct_defs
            .get(module)
            .expect("struct defs should be readable right after they are defined");
        self.tel.execute(
            &["fz", "compiler2", "struct_def", "defined"],
            &measurements! {
                module_id: module.as_u32(),
                field_count: def.fields.len(),
                changed: changed as u64,
            },
            &metadata! {
                def: opaque_debug(def),
            },
        );
        changed
    }

    /// The precise, durable reader over `defstruct`'s ordered fields:
    /// `resolve.rs`'s `TypeExpr::StructRecord` classification reads this, not
    /// `module_struct_fields`'s source scan, once it needs the schema
    /// (fz-rh2.17.5.6.10). Unlike that scan, this never has an opinion when
    /// the fact has not published yet — callers that need the answer wait on
    /// `FactKey::StructDefined(module)` first (see `jobs::types::derive_type_def`).
    pub(crate) fn struct_def_fields(&self, module: ModuleId) -> Option<&[String]> {
        self.struct_defs.get(module).map(|def| def.fields.as_slice())
    }

    /// Records that `field` was referenced on `module`'s struct from
    /// `requester`, mirroring `note_module_interface_expectation`. `A`'s
    /// `defstruct` has no dedicated re-derivation job to rewake the way
    /// `ModuleInterface` does when a late expectation lands, so this method
    /// is half of validate-on-settle: reference-then-settle is validated in
    /// `validate_struct_field_expectations` when `A` finally publishes;
    /// settle-then-reference (`A` already published) is checked right here,
    /// immediately, since nothing else would ever re-check it otherwise.
    pub(crate) fn note_struct_field_expectation(
        &mut self,
        module: ModuleId,
        field: String,
        requester: InterfaceRequester,
    ) -> Result<(), FatalError> {
        self.struct_expectations
            .record(module, StructFieldExpectation { field, requester });
        if self.struct_defs.get(module).is_some() {
            self.validate_struct_field_expectations(module)?;
        }
        Ok(())
    }

    /// Checks every outstanding field obligation on `module` against its
    /// published `defstruct` schema, mirroring
    /// `validate_module_interface_expectations`: a field named on a struct
    /// that does not declare it is diagnosed at the *requester's* span,
    /// independent of whether the struct or the reference settled first. A
    /// no-op until `module`'s `defstruct` has actually published. Every bad
    /// obligation is reported in one pass (two requesters each naming a bad
    /// field both surface), then the job is failed once.
    pub(crate) fn validate_struct_field_expectations(&self, module: ModuleId) -> Result<(), FatalError> {
        let Some(def) = self.struct_defs.get(module) else {
            return Ok(());
        };
        let mut violated = false;
        for expectation in self.struct_expectations.expectations(module) {
            if def.fields.iter().any(|field| field == &expectation.field) {
                continue;
            }
            let module_name = self
                .module_name(module)
                .map(str::to_owned)
                .unwrap_or_else(|| format!("<unnamed module {}>", module.as_u32()));
            emit_through(
                self.tel,
                std::slice::from_ref(&Diagnostic::error(
                    codes::RESOLVE_UNKNOWN_STRUCT_FIELD,
                    format!("struct `{}` has no field `{}`", module_name, expectation.field),
                    expectation.requester.span,
                )),
            );
            violated = true;
        }
        if violated { Err(FatalError) } else { Ok(()) }
    }

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

    pub(crate) fn define_protocol_dispatch(&mut self, protocol: ModuleId, dispatch: ProtocolDispatch) -> bool {
        let changed = self.protocol_dispatches.define(protocol, dispatch);
        let dispatch = self
            .protocol_dispatches
            .get(protocol)
            .expect("protocol dispatches should be readable right after they are defined");
        self.tel.execute(
            &["fz", "compiler2", "protocol_dispatch", "defined"],
            &measurements! {
                protocol_id: protocol.as_u32(),
                arms: dispatch.arms.len(),
                changed: changed as u64,
            },
            &metadata! {
                dispatch: opaque_debug(dispatch),
            },
        );
        changed
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

    fn is_protocol_domain_type(&self, name: &TypeName) -> bool {
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

    fn emit_type_referenced(&self, consumer_kind: &'static str, consumer_name: &str, referenced: &TypeName) {
        self.tel.execute(
            &["fz", "compiler2", "type", "referenced"],
            &measurements! {
                ref_module_id: referenced.module.as_u32(),
                ref_arity: referenced.arity,
            },
            &metadata! {
                ref_name: &referenced.name,
                consumer_kind: consumer_kind,
                consumer: consumer_name,
                referenced: opaque_debug(referenced),
            },
        );
    }

    pub(crate) fn define_function(
        &mut self,
        id: FunctionId,
        source: FunctionSource,
        expanded_source: FunctionSource,
        surface: FunctionSurface,
    ) -> bool {
        let module = self.functions.reference_for(id).module;
        let owner_module = source.owner_module;
        let code = source.code;
        let arity = surface.arity();
        let clauses = surface.clauses.len();
        let changed = self.functions.define(id, source, expanded_source, surface);
        if changed {
            let function = self.functions.get(id);
            let function_ref = self.functions.reference_for(id);
            self.tel.execute(
                &["fz", "compiler2", "function", "defined"],
                &measurements! {
                    code_id: code.as_u32(),
                    module_id: module.as_u32(),
                    owner_module_id: owner_module.as_u32(),
                    function_id: id.as_u32(),
                    arity: arity,
                    clauses: clauses,
                    source_heap_id: function.state_source_heap_id().unwrap_or_default(),
                    source_root_ref: function.state_source_root_word().unwrap_or_default(),
                },
                &metadata! {
                    function: opaque_debug(function),
                    function_ref: opaque_debug(function_ref),
                    function_id: opaque_debug(&id),
                    module_id: opaque_debug(&module),
                    owner_module_id: opaque_debug(&owner_module),
                },
            );
        }
        changed
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
    pub(crate) fn stash_function_source(&mut self, function: FunctionId, source: FunctionSource) -> bool {
        let function_ref = self.functions.reference_for(function);
        let source_owner_module = source.owner_module;
        let source_module_id = function_ref.module;
        // The eager interface-tier signal: this function's identity and interface
        // are published at scope time even though the body stays cold until a
        // consumer pulls it (fz-f98.14.5). It mirrors the `function.source.noted`
        // shape so name-keyed observers see every scope-defined function, and it
        // is the surface counterpart to `type.noted`.
        self.tel.execute(
            &["fz", "compiler2", "function", "source", "stashed"],
            &measurements! {
                code_id: source.code.as_u32(),
                module_id: function_ref.module.as_u32(),
                owner_module_id: source.owner_module.as_u32(),
                function_id: function.as_u32(),
                arity: function_ref.arity,
                clauses: function_source_clause_count(&source),
                source_heap_id: source.source.key().heap_id,
                source_root_ref: source.source.root().raw_word(),
            },
            &metadata! {
                function_ref: opaque_debug(function_ref),
                source: opaque_debug(&source),
                function_id: opaque_debug(&function),
                module_id: opaque_debug(&source_module_id),
                owner_module_id: opaque_debug(&source_owner_module),
            },
        );
        self.pending_function_sources.stash(function, source)
    }

    pub(crate) fn pending_function_source(&self, function: FunctionId) -> Option<&FunctionSource> {
        self.pending_function_sources.get(function)
    }

    /// Promotes a stashed source into the consumable `FunctionSource` fact when a
    /// reached consumer demands the body. Returns `true` when the fact's content
    /// changed, so the caller publishes the change to the scheduler.
    pub(crate) fn publish_pending_function_source(&mut self, function: FunctionId) -> Option<bool> {
        let source = self.pending_function_sources.get(function).cloned()?;
        Some(self.note_function_source(function, source))
    }

    pub(crate) fn note_function_source(&mut self, function: FunctionId, source: FunctionSource) -> bool {
        let changed = self.functions.note(function, source);
        let source = match self.functions.get(function) {
            super::identity::FunctionState::Noted { source }
            | super::identity::FunctionState::Defined { source, .. } => source.as_ref(),
            super::identity::FunctionState::Placeholder => {
                unreachable!("noting a function source always leaves the function noted or defined")
            }
        };
        let function_ref = self.functions.reference_for(function);
        let source_owner_module = source.owner_module;
        let source_module_id = function_ref.module;
        self.tel.execute(
            &["fz", "compiler2", "function", "source", "noted"],
            &measurements! {
                code_id: source.code.as_u32(),
                module_id: function_ref.module.as_u32(),
                owner_module_id: source.owner_module.as_u32(),
                function_id: function.as_u32(),
                arity: function_ref.arity,
                clauses: function_source_clause_count(source),
                source_heap_id: source.source.key().heap_id,
                source_root_ref: source.source.root().raw_word(),
                changed: changed as u64,
            },
            &metadata! {
                function_ref: opaque_debug(function_ref),
                source: opaque_debug(source),
                function_id: opaque_debug(&function),
                module_id: opaque_debug(&source_module_id),
                owner_module_id: opaque_debug(&source_owner_module),
            },
        );
        changed
    }

    pub(crate) fn function_source(&self, function: FunctionId) -> Option<FunctionSource> {
        match self.functions.get(function) {
            super::identity::FunctionState::Noted { source }
            | super::identity::FunctionState::Defined { source, .. } => Some(*source.clone()),
            super::identity::FunctionState::Placeholder => None,
        }
    }

    pub(crate) fn note_expanded_function_source(&mut self, function: FunctionId, source: FunctionSource) -> bool {
        let changed = self.expanded_function_sources.define(function, source);
        let source = self
            .expanded_function_sources
            .get(function)
            .expect("expanded function sources should be readable right after they are defined");
        let function_ref = self.functions.reference_for(function);
        self.tel.execute(
            &["fz", "compiler2", "function", "source", "expanded"],
            &measurements! {
                code_id: source.code.as_u32(),
                module_id: function_ref.module.as_u32(),
                owner_module_id: source.owner_module.as_u32(),
                function_id: function.as_u32(),
                arity: function_ref.arity,
                clauses: function_source_clause_count(source),
                source_heap_id: source.source.key().heap_id,
                source_root_ref: source.source.root().raw_word(),
                changed: changed as u64,
            },
            &metadata! {
                function_ref: opaque_debug(function_ref),
                source: opaque_debug(source),
                function_id: opaque_debug(&function),
            },
        );
        changed
    }

    pub(crate) fn expanded_function_source(&self, function: FunctionId) -> Option<FunctionSource> {
        self.expanded_function_sources.get(function).cloned()
    }

    pub(crate) fn define_function_contract(&mut self, function: FunctionId, contract: FunctionContract) -> bool {
        let changed = self.function_contracts.define(function, contract);
        let contract = self
            .function_contracts
            .get(function)
            .expect("function contracts should be readable right after they are defined");
        let function_ref = self.functions.reference_for(function);
        self.tel.execute(
            &["fz", "compiler2", "function_contract", "defined"],
            &measurements! {
                function_id: function.as_u32(),
                arity: function_ref.arity,
                changed: changed as u64,
            },
            &metadata! {
                function_ref: opaque_debug(function_ref),
                contract: opaque_debug(contract),
            },
        );
        changed
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

    pub(crate) fn define_protocol_callback(&mut self, function: FunctionId, protocol: ModuleId) {
        let callback = ProtocolCallback { protocol };
        self.protocol_callbacks.define(function, callback);
        let function_ref = self.functions.reference_for(function);
        self.tel.execute(
            &["fz", "compiler2", "protocol_callback", "defined"],
            &measurements! {
                protocol_id: protocol.as_u32(),
                function_id: function.as_u32(),
                arity: function_ref.arity,
            },
            &metadata! {
                callback: opaque_debug(&callback),
                function_ref: opaque_debug(function_ref),
            },
        );
    }

    pub(crate) fn protocol_callback(&self, function: FunctionId) -> Option<ProtocolCallback> {
        self.protocol_callbacks.get(function)
    }

    pub(crate) fn define_protocol_impl(
        &mut self,
        protocol: ModuleId,
        target: ModuleId,
        callbacks: HashMap<FunctionId, ProtocolCallbackImpl>,
    ) {
        let key = ProtocolImplKey { protocol, target };
        self.protocol_impls.define(key, ProtocolImpl { callbacks });
        let protocol_impl = self
            .protocol_impls
            .impl_for(&key)
            .expect("protocol impls should be readable right after they are defined");
        self.tel.execute(
            &["fz", "compiler2", "protocol_impl", "defined"],
            &measurements! {
                protocol_id: protocol.as_u32(),
                target_id: target.as_u32(),
                callbacks: protocol_impl.callbacks.len(),
            },
            &metadata! {
                key: opaque_debug(&key),
                protocol_impl: opaque_debug(protocol_impl),
            },
        );
    }

    pub(crate) fn protocol_impls_for(&self, protocol: ModuleId) -> Vec<(ProtocolImplKey, ProtocolImpl)> {
        self.protocol_impls
            .impls_for_protocol(protocol)
            .map(|(key, protocol_impl)| (*key, protocol_impl.clone()))
            .collect()
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
        let owner_code = owner_source.code;
        let id = self
            .functions
            .reference_generated(owner, owner_module, surface.span, surface.arity());
        let fn_source = FunctionSource {
            code: owner_code,
            owner_module: owner_source.owner_module,
            namespace,
            capture_params,
            required_remote_macros: owner_source.required_remote_macros.clone(),
            variadic: surface.variadic,
            source: owner_source.source.clone(),
        };
        let arity = surface.arity();
        let clauses = surface.clauses.len();
        let changed = self.functions.define(id, fn_source.clone(), fn_source, surface);
        if changed {
            let function = self.functions.get(id);
            let function_ref = self.functions.reference_for(id);
            self.tel.execute(
                &["fz", "compiler2", "function", "defined"],
                &measurements! {
                    code_id: owner_code.as_u32(),
                    module_id: owner_module.as_u32(),
                    owner_module_id: owner_source.owner_module.as_u32(),
                    function_id: id.as_u32(),
                    arity: arity,
                    clauses: clauses,
                    owner_function_id: owner.as_u32(),
                    source_heap_id: function.state_source_heap_id().unwrap_or_default(),
                    source_root_ref: function.state_source_root_word().unwrap_or_default(),
                },
                &metadata! {
                    function: opaque_debug(function),
                    function_ref: opaque_debug(function_ref),
                    function_id: opaque_debug(&id),
                    module_id: opaque_debug(&owner_module),
                    owner_module_id: opaque_debug(&owner_source.owner_module),
                    owner_function_id: opaque_debug(&owner),
                },
            );
        }
        (id, changed)
    }

    pub(crate) fn define_lowered_body(&mut self, function: FunctionId, body: LoweredBody) -> bool {
        let changed = self.bodies.define(function, body);
        let body = match self.bodies.get(function) {
            Some(super::body::BodyState::Lowered(body)) => body,
            _ => unreachable!("defining a lowered body always leaves the body lowered"),
        };
        let function_ref = self.functions.reference_for(function);
        let slot = self.functions.get(function);
        let (fn_source, fn_surface) = match slot {
            super::identity::FunctionState::Defined { source, surface, .. } => (source.as_ref(), surface),
            super::identity::FunctionState::Placeholder | super::identity::FunctionState::Noted { .. } => {
                panic!("lowered bodies should only be defined for known functions")
            }
        };
        let (clauses, generated, arity) = match body {
            LoweredBody::Extern { signature } => (0_usize, 0_usize, signature.params.len()),
            LoweredBody::Clauses { clauses, generated, .. } => (clauses.len(), generated.len(), fn_surface.arity()),
        };
        self.tel.execute(
            &["fz", "compiler2", "lowered_body", "defined"],
            &measurements! {
                code_id: fn_source.code.as_u32(),
                module_id: function_ref.module.as_u32(),
                function_id: function.as_u32(),
                arity: arity,
                clauses: clauses,
                generated: generated,
                source_root_ref: fn_source.source.root().raw_word(),
            },
            &metadata! {
                function_ref: opaque_debug(function_ref),
                body: opaque_debug(body),
                function_id: opaque_debug(&function),
            },
        );
        changed
    }

    pub(crate) fn define_guard_dispatch(&mut self, function: FunctionId, dispatch: PatternGuardDispatch<Ty>) -> bool {
        let changed = self.guard_dispatches.define(function, dispatch);
        let dispatch = self
            .guard_dispatches
            .get(function)
            .expect("guard dispatches should be readable right after they are defined");
        let function_ref = self.functions.reference_for(function);
        let slot = self.functions.get(function);
        let (fn_source, fn_surface) = match slot {
            super::identity::FunctionState::Defined { source, surface, .. } => (source.as_ref(), surface),
            super::identity::FunctionState::Placeholder | super::identity::FunctionState::Noted { .. } => {
                panic!("guard dispatch should only be defined for known functions")
            }
        };
        self.tel.execute(
            &["fz", "compiler2", "guard_dispatch", "defined"],
            &measurements! {
                code_id: fn_source.code.as_u32(),
                module_id: function_ref.module.as_u32(),
                function_id: function.as_u32(),
                arity: fn_surface.arity(),
                bodies: dispatch.bodies.len(),
                guards: dispatch.plan.guards.len(),
                pinned: dispatch.plan.pinned.len(),
                source_root_ref: fn_source.source.root().raw_word(),
            },
            &metadata! {
                function_ref: opaque_debug(function_ref),
                dispatch: opaque_debug(dispatch),
                function_id: opaque_debug(&function),
            },
        );
        changed
    }

    pub(crate) fn define_entry_dispatch(&mut self, function: FunctionId, plan: PatternDispatchPlan<Ty>) -> bool {
        let changed = self.entry_dispatches.define(function, plan);
        let plan = self
            .entry_dispatches
            .get(function)
            .expect("entry dispatches should be readable right after they are defined");
        let function_ref = self.functions.reference_for(function);
        let slot = self.functions.get(function);
        let (fn_source, fn_surface) = match slot {
            super::identity::FunctionState::Defined { source, surface, .. } => (source.as_ref(), surface),
            super::identity::FunctionState::Placeholder | super::identity::FunctionState::Noted { .. } => {
                panic!("entry dispatch should only be defined for known functions")
            }
        };
        self.tel.execute(
            &["fz", "compiler2", "entry_dispatch", "defined"],
            &measurements! {
                code_id: fn_source.code.as_u32(),
                module_id: function_ref.module.as_u32(),
                function_id: function.as_u32(),
                arity: fn_surface.arity(),
                outcomes: plan.outcomes.len(),
                guards: plan.guards.len(),
                pinned: plan.pinned.len(),
                source_root_ref: fn_source.source.root().raw_word(),
            },
            &metadata! {
                function_ref: opaque_debug(function_ref),
                plan: opaque_debug(plan),
                function_id: opaque_debug(&function),
            },
        );
        changed
    }

    pub(crate) fn define_recursive(&mut self, function: FunctionId, recursive: bool) -> bool {
        self.recursive.define(function, recursive)
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

    pub(crate) fn module_struct_fields(&self, module: ModuleId) -> Option<&[String]> {
        match self.modules.get(module) {
            ModuleState::Placeholder { .. } => None,
            ModuleState::Indexed { source, .. }
            | ModuleState::Scoped { source, .. }
            | ModuleState::Defined { source, .. } => match &source.kind {
                ModuleSourceKind::Protocol(_) | ModuleSourceKind::ProtocolImpl(_) => None,
                ModuleSourceKind::Body(body) => body.forms.iter().find_map(|form| match form {
                    super::quoted_surface::ScopeForm::Struct(def) => Some(def.fields.as_slice()),
                    _ => None,
                }),
            },
        }
    }

    pub(crate) fn module_name(&self, module: ModuleId) -> Option<&str> {
        self.modules.name(module)
    }

    pub(crate) fn struct_schemas(&self) -> BTreeMap<String, Vec<String>> {
        self.modules.named_struct_schemas()
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
    pub(crate) fn demand_function_scope(&mut self, function: FunctionId) -> Vec<FactKey> {
        let module = self.function_module(function);
        if module.is_global() {
            let function_ref = self.function_ref(function).clone();
            let mut certain_home = None;
            let mut opaque_candidates = Vec::new();
            let mut pending = Vec::new();
            for code_id in self.code.ids() {
                match self.code.get(code_id) {
                    CodeState::Pending => pending.push(FactKey::CodeIndexed(code_id)),
                    CodeState::Indexed { source } => match code_surface_function_match(source, &function_ref) {
                        FunctionSurfaceMatch::Certain => {
                            certain_home.get_or_insert(code_id);
                        }
                        FunctionSurfaceMatch::Opaque => opaque_candidates.push(code_id),
                        FunctionSurfaceMatch::None => {}
                    },
                    // A Scoped home is unreachable here: this walk runs only
                    // when the pending source stash is empty, and scoping a
                    // code eagerly stashes every function it defines
                    // (source_publish), so once the home reaches Scoped the
                    // caller never re-enters.
                    CodeState::Scoped { .. } => {}
                }
            }
            // A certain home resolves the function for sure once scoped, so
            // every opaque candidate and pending code is irrelevant — naming
            // them too would be over-demand.
            if let Some(code_id) = certain_home {
                return vec![FactKey::CodeScoped(code_id)];
            }
            // Opaque item-macro calls are only MAYBE the home (fz-go4.43):
            // probe them one at a time, in submission order, instead of
            // scoping every opaque candidate in the program up front. Once
            // this single wait is satisfied, `publish_function_source_job`
            // re-runs and re-enters this scan: the probed code is now
            // `Scoped` (excluded above), so an unresolved name narrows to the
            // NEXT candidate, and a name the probe just produced short-circuits
            // here instead of forcing every other candidate to expand too.
            if let Some(code_id) = opaque_candidates.into_iter().next() {
                return vec![FactKey::CodeScoped(code_id)];
            }
            return pending;
        }
        if self.module_has_source_state(module) || self.ensure_runtime_module(module).is_some() {
            return vec![FactKey::ModuleDefined(module)];
        }
        Vec::new()
    }

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
    pub(crate) fn wait_for_type_decl(&mut self, module: ModuleId) -> JobEffects {
        self.ensure_runtime_module(module);
        JobEffects::wait_on_current(FactKey::ModuleDefined(module))
    }

    pub fn fact_revision(&self, key: &FactKey) -> Option<u64> {
        self.work_graph.facts().revision(key)
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
        let recursive = *self
            .recursive
            .get(function)
            .expect("activation keying should wait for recursive facts before activation");
        // The arrow is the PRECISE evidence: address the whole input vector in one
        // pass (fz-hwn.27.6), so two distinct inference vars `[Ty27,Ty28]` address
        // to distinct `[a0,a1]` and never collapse to the phantom `[a0,a0]`.
        let key = super::identity::ActivationKey::from_inputs(root, function, inputs, &mut self.types);
        if !recursive {
            return key;
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

    pub(crate) fn ensure_runtime_module(&mut self, module: ModuleId) -> Option<CodeId> {
        let slot = self.runtime_modules.get(&module)?;
        if let Some(code_id) = slot.code_id {
            return Some(code_id);
        }

        let name = slot.name;
        let source = slot.source;
        let source_name = format!("runtime:{name}.fz");
        // Register the runtime module's source WITHOUT enqueuing IndexCode/
        // ScopeCode. This runs mid-job (a callee type implying an unloaded
        // runtime module), so an eager enqueue here would be a job commanding
        // work to start — a push mislabeled as the external front door. Every
        // caller registers a `wait_on_current(CodeIndexed(code_id))` (or a
        // `ModuleDefined` wait that chains to it through `define_module`), and
        // `demand_fact_producer` maps `CodeIndexed -> IndexCode`, so the
        // drain/stall pull mints the module as a `BlockedWaiterExpansion` —
        // the eager enqueue bought nothing.
        let code_id = self.register_code(Some(source_name), source.to_string());
        self.runtime_modules
            .get_mut(&module)
            .expect("runtime module should still exist while recording its code id")
            .code_id = Some(code_id);
        Some(code_id)
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

    pub(crate) fn module_struct_value_ty(&mut self, module: ModuleId, field_tys: &[Ty]) -> Ty {
        let name = self
            .module_name(module)
            .unwrap_or_else(|| panic!("named struct module {} should have a reverse lookup", module.as_u32()))
            .to_string();
        let field_names = self
            .module_struct_fields(module)
            .map(|fields| fields.to_vec())
            .unwrap_or_default();
        self.struct_value_ty(&name, &field_names, field_tys)
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
    /// (`field_names`/`field_tys` in schema order) — the fact-backed sibling
    /// of `module_struct_value_ty`, which still derives its field names from
    /// the `module_struct_fields` source scan for the struct-literal lowering
    /// consumer that has not migrated yet.
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
            .expectations(module)
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

    fn unresolved_module_issue(&self, module: ModuleId) -> UnresolvedIssue {
        UnresolvedIssue {
            key: UnresolvedIssueKey::Module(module),
            diagnostic: Diagnostic::error(
                codes::RESOLVE_UNKNOWN_MODULE,
                format!(
                    "module `{}` is not defined",
                    self.module_name(module)
                        .expect("referenced modules should have reverse names")
                ),
                Span::DUMMY,
            ),
        }
    }

    fn unresolved_function_issue(&self, frontier: &HashSet<FactKey>, function: FunctionId) -> Option<UnresolvedIssue> {
        let function_ref = self.function_ref(function);
        if function_ref.module.is_global() {
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
        Some(UnresolvedIssue {
            key: UnresolvedIssueKey::Export(function),
            diagnostic: Diagnostic::error(
                codes::RESOLVE_UNKNOWN_IMPORT,
                format!(
                    "module `{}` does not export `{}/{}`",
                    module_name, function_ref.name, function_ref.arity
                ),
                Span::DUMMY,
            ),
        })
    }
}

fn emit_job_diagnostic(world: &World<'_>, diagnostic: Diagnostic) -> FatalError {
    emit_through(world.tel(), std::slice::from_ref(&diagnostic));
    FatalError
}

fn dedupe_job_facts(facts: Vec<FactKey>) -> Vec<FactKey> {
    facts.into_iter().collect::<HashSet<_>>().into_iter().collect()
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

fn function_source_clause_count(source: &FunctionSource) -> u64 {
    let Ok(items) = source.source.cursor().list_items() else {
        return 0;
    };
    let mut clauses = 0_u64;
    for item in items {
        let Ok(Some(node)) = item.ast_node() else {
            continue;
        };
        let Ok(head) = node.head.atom_name() else {
            continue;
        };
        if head.starts_with('@') {
            continue;
        }
        if head == "extern" {
            return 0;
        }
        clauses += 1;
    }
    clauses
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
