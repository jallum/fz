//! Compiler2's owned world state.
//!
//! Compiler-owned identities are total here. A `CodeId`, `ModuleId`,
//! `FunctionId`, or `RootId` that came from Compiler2 must resolve; a bad id is
//! a bug and should panic at the lookup boundary. `Option` is reserved for
//! legitimate state absence like "this known function is still a placeholder"
//! or "this known code has not been indexed yet".

use std::cmp::Reverse;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::ast::FnDef;
use crate::ast::Item;
use crate::compiler::source::Span;
use crate::diag::driver::emit_through;
use crate::diag::{Diagnostic, codes};
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardDispatch};
use crate::modules::runtime_library;
use crate::telemetry::{Telemetry, opaque};
use crate::type_expr::{ModuleTypeEnv, build_module_type_env_for_with_base, builtin_type_env};
use crate::{measurements, metadata};

use super::CodeId;
use super::artifact::{
    AbiReadyProgram, AbiReadyProgramMap, EmissionReadyProgram, EmissionReadyProgramMap, MaterializedProgram,
    MaterializedProgramMap,
};
use super::body::{LoweredBody, LoweredBodyMap};
use super::code::CodeMap;
use super::deps::UnresolvedWait;
use super::dispatch::{EntryDispatchMap, GuardDispatchMap};
use super::drive::{FactKey, Job, JobEffects, WorkGraph};
use super::facts::FactValue;
use super::identity::{
    ActivationKey, ExecutableNeed, FunctionDef, FunctionId, FunctionMap, ModuleExport, ModuleId, ModuleMap,
    ModuleSourceKind, ModuleState, RootEntry, RootId, RootMap,
};
use super::keying::{DispatchMaskMap, RecursiveMap};
use super::namespace::{Namespace, NamespaceStore, NamespaceSymbol};
use super::protocol::{
    ProtocolCallback, ProtocolCallbackImpl, ProtocolCallbackMap, ProtocolImpl, ProtocolImplKey, ProtocolImplMap,
};
use super::runtime::{self, RuntimeModuleCode};
use super::semantic::{
    ActivationAnalysis, ActivationMap, CallSiteKey, CallSiteMap, CallSiteSummary, SemanticClosure, SemanticClosureMap,
};
use super::types::{ClosureTarget, Ty, Types};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum UnresolvedIssueKey {
    Module(ModuleId),
    Function(FunctionId),
    Export(FunctionId),
}

struct UnresolvedIssue {
    key: UnresolvedIssueKey,
    diagnostic: Diagnostic,
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
    bodies: LoweredBodyMap,
    guard_dispatches: GuardDispatchMap,
    entry_dispatches: EntryDispatchMap,
    recursive: RecursiveMap,
    dispatch_masks: DispatchMaskMap,
    protocol_callbacks: ProtocolCallbackMap,
    protocol_impls: ProtocolImplMap,
    activations: ActivationMap,
    callsites: CallSiteMap,
    semantic_closures: SemanticClosureMap,
    artifacts: MaterializedProgramMap,
    abi_ready: AbiReadyProgramMap,
    emission_ready: EmissionReadyProgramMap,
    roots: RootMap,
    namespaces: NamespaceStore,
    types: Types,
    runtime_prelude: CodeId,
    runtime_modules: HashMap<ModuleId, RuntimeModuleCode>,
    reported_unresolved: HashSet<UnresolvedIssueKey>,
    pub(crate) work_graph: WorkGraph,
}

impl std::fmt::Debug for World<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("World")
            .field("code", &self.code)
            .field("modules", &self.modules)
            .field("functions", &self.functions)
            .field("bodies", &self.bodies)
            .field("roots", &self.roots)
            .field("namespaces", &self.namespaces)
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
            bodies: LoweredBodyMap::new(),
            guard_dispatches: GuardDispatchMap::new(),
            entry_dispatches: EntryDispatchMap::new(),
            recursive: RecursiveMap::new(),
            dispatch_masks: DispatchMaskMap::new(),
            protocol_callbacks: ProtocolCallbackMap::new(),
            protocol_impls: ProtocolImplMap::new(),
            activations: ActivationMap::new(),
            callsites: CallSiteMap::new(),
            semantic_closures: SemanticClosureMap::new(),
            artifacts: MaterializedProgramMap::new(),
            abi_ready: AbiReadyProgramMap::new(),
            emission_ready: EmissionReadyProgramMap::new(),
            roots: RootMap::new(),
            namespaces: NamespaceStore::new(),
            types: Types::new(),
            runtime_prelude: CodeId::ZERO,
            runtime_modules: HashMap::new(),
            reported_unresolved: HashSet::new(),
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

    pub(crate) fn types(&self) -> &Types {
        &self.types
    }

    pub(crate) fn types_mut(&mut self) -> &mut Types {
        &mut self.types
    }

    pub fn submit_code(&mut self, name: Option<String>, text: String) -> CodeId {
        let bytes = text.len() as u64;
        let code_id = self.code.define(name, text);
        self.work_graph.enqueue(Job::IndexCode(code_id));
        if !self.roots.is_empty() {
            self.work_graph.enqueue(Job::ScopeCode(code_id));
        }
        self.tel.execute(
            &["fz", "compiler2", "code", "submitted"],
            &measurements! {
                code_id: code_id.as_u32() as u64,
                bytes: bytes,
            },
            &metadata! {},
        );
        code_id
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
        let function = self.reference_function(module, name.clone(), arity);
        let root_id = self.roots.define(RootEntry { function, need });
        for code_id in self.code.ids() {
            self.work_graph.enqueue(Job::ScopeCode(code_id));
        }
        self.work_graph.enqueue(Job::SeedRoot(root_id));
        let root = self.roots.get(root_id);
        let function_ref = self.functions.reference_for(function);
        self.tel.execute(
            &["fz", "compiler2", "root", "submitted"],
            &measurements! {
                root_id: root_id.as_u32() as u64,
                module_id: module.as_u32() as u64,
                function_id: function.as_u32() as u64,
                arity: arity as u64,
                pending_codes: self.code.len() as u64,
            },
            &metadata! {
                root: opaque(root),
                function_ref: opaque(function_ref),
            },
        );
        root_id
    }

    pub(crate) fn complete_job(&mut self, job: Job, effects: JobEffects) -> super::AppliedStep<Job, FactKey> {
        let reads = effects.reads.into_iter().collect();
        let waits = effects.waits.into_iter().collect();
        let step = self.work_graph.complete(
            &mut self.types,
            job.clone(),
            reads,
            waits,
            effects.outputs,
            effects.follow_up,
        );
        self.tel.event(
            &["fz", "compiler2", "work_graph", "applied"],
            metadata! {
                job: opaque(&job),
                step: opaque(&step),
            },
        );
        step
    }

    pub fn demand(&mut self, job: Job) -> bool {
        self.work_graph.enqueue(job)
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
            emit_through(self.tel, None, &diagnostics);
        }
        self.reported_unresolved = next;
    }

    pub(crate) fn clear_unresolved_diagnostics(&mut self) {
        self.reported_unresolved.clear();
    }

    pub fn code_name(&self, id: CodeId) -> Option<&str> {
        self.code.name(id)
    }

    pub fn code_text(&self, id: CodeId) -> &str {
        self.code.text(id)
    }

    pub fn root_entry(&self, id: RootId) -> RootEntry {
        self.roots.get(id).entry
    }

    pub fn root_revision(&self, id: RootId) -> u64 {
        self.roots.get(id).revision
    }

    pub(crate) fn activation_key(&mut self, root: RootId, function: FunctionId, inputs: &[Ty]) -> ActivationKey {
        self.canonical_activation_key(root, function, inputs)
    }

    pub(crate) fn activation_inputs(&self, key: &ActivationKey) -> Option<Vec<Ty>> {
        match self
            .work_graph
            .facts()
            .slot(&FactKey::Activation(key.clone()))
            .and_then(|slot| slot.value())
        {
            Some(FactValue::Inputs(inputs)) => Some(inputs.clone()),
            Some(FactValue::Presence(_)) => panic!("activation facts should carry input values"),
            None => None,
        }
    }

    pub fn activation_analysis(&self, key: &ActivationKey) -> Option<&ActivationAnalysis> {
        self.activations.get(key).and_then(|slot| slot.analysis())
    }

    pub fn activation_return(&self, key: &ActivationKey) -> Option<Ty> {
        self.fact_revision(FactKey::ReturnType(key.clone()))?;
        self.activations.get(key).and_then(|slot| slot.return_ty().cloned())
    }

    pub fn define_activation_analysis(&mut self, key: &ActivationKey, mut analysis: ActivationAnalysis) -> u64 {
        for ty in analysis.value_types.values_mut() {
            *ty = self.types.alpha_normalize_vars(ty);
        }
        let revision = self.activations.define_analysis(key, analysis.clone());
        self.tel.execute(
            &["fz", "compiler2", "activation_analysis", "defined"],
            &measurements! {
                root_id: key.root.as_u32() as u64,
                function_id: key.function.as_u32() as u64,
                revision: revision,
                reachable_clauses: analysis.reachable_clauses.len() as u64,
                callsites: analysis.callsites.len() as u64,
                values: analysis.value_types.len() as u64,
            },
            &metadata! {
                activation: opaque(key),
                analysis: opaque(&analysis),
            },
        );
        revision
    }

    pub fn define_activation_return(&mut self, key: &ActivationKey, return_ty: Ty) -> u64 {
        let return_ty = self.types.alpha_normalize_vars(&return_ty);
        let revision = self.activations.define_return(&mut self.types, key, return_ty);
        self.tel.execute(
            &["fz", "compiler2", "return_type", "defined"],
            &measurements! {
                root_id: key.root.as_u32() as u64,
                function_id: key.function.as_u32() as u64,
                revision: revision,
            },
            &metadata! {
                activation: opaque(key),
                return_ty: opaque(&return_ty),
            },
        );
        revision
    }

    pub fn define_callsite_summary(&mut self, key: CallSiteKey, mut summary: CallSiteSummary) -> u64 {
        summary.input_types = summary
            .input_types
            .into_iter()
            .map(|input| self.types.alpha_normalize_vars(&input))
            .collect();
        summary.return_ty = self.types.alpha_normalize_vars(&summary.return_ty);
        let revision = self.callsites.define(key.clone(), summary.clone());
        self.tel.execute(
            &["fz", "compiler2", "callsite", "defined"],
            &measurements! {
                root_id: key.activation.root.as_u32() as u64,
                function_id: key.activation.function.as_u32() as u64,
                callsite_id: key.callsite.as_u32() as u64,
                revision: revision,
                input_arity: summary.input_types.len() as u64,
            },
            &metadata! {
                callsite: opaque(&key),
                summary: opaque(&summary),
            },
        );
        revision
    }

    pub fn callsite_summary(&self, key: &CallSiteKey) -> Option<&CallSiteSummary> {
        self.callsites.get(key)
    }

    pub(crate) fn define_semantic_closure(
        &mut self,
        root: RootId,
        closure: SemanticClosure,
        dependencies: super::semantic::DependencySnapshot,
    ) -> u64 {
        let revision = self.semantic_closures.define(root, closure.clone(), dependencies);
        self.tel.execute(
            &["fz", "compiler2", "semantic_closed", "defined"],
            &measurements! {
                root_id: root.as_u32() as u64,
                revision: revision,
            },
            &metadata! {
                closure: opaque(&closure),
            },
        );
        revision
    }

    pub(crate) fn semantic_closure(&self, root: RootId) -> SemanticClosure {
        self.semantic_closures
            .get(root)
            .cloned()
            .expect("semantic closures should only be read after their fact is defined")
    }

    pub(crate) fn semantic_closure_dependencies(&self, root: RootId) -> &super::semantic::DependencySnapshot {
        self.semantic_closures
            .dependencies(root)
            .expect("semantic closure dependencies should only be read after their fact is defined")
    }

    pub(crate) fn define_materialized_program(&mut self, root: RootId, program: MaterializedProgram) -> u64 {
        let revision = self.artifacts.define(root, program.clone());
        self.tel.execute(
            &["fz", "compiler2", "materialized_program", "defined"],
            &measurements! {
                root_id: root.as_u32() as u64,
                revision: revision,
                executable_count: program.executables.len() as u64,
            },
            &metadata! {
                program: opaque(&program),
            },
        );
        revision
    }

    pub(crate) fn materialized_program(&self, root: RootId) -> MaterializedProgram {
        self.artifacts
            .get(root)
            .cloned()
            .expect("materialized programs should only be read after their fact is defined")
    }

    pub(crate) fn define_abi_ready_program(&mut self, root: RootId, program: AbiReadyProgram) -> u64 {
        let revision = self.abi_ready.define(root, program.clone());
        self.tel.execute(
            &["fz", "compiler2", "abi_ready_program", "defined"],
            &measurements! {
                root_id: root.as_u32() as u64,
                revision: revision,
                executable_count: program.executables.len() as u64,
                callable_entry_count: program.callable_entries.len() as u64,
            },
            &metadata! {
                program: opaque(&program),
            },
        );
        revision
    }

    pub(crate) fn abi_ready_program(&self, root: RootId) -> AbiReadyProgram {
        self.abi_ready
            .get(root)
            .cloned()
            .expect("ABI-ready programs should only be read after their fact is defined")
    }

    pub(crate) fn define_emission_ready_program(&mut self, root: RootId, program: EmissionReadyProgram) -> u64 {
        let revision = self.emission_ready.define(root, program.clone());
        self.tel.execute(
            &["fz", "compiler2", "emission_ready_program", "defined"],
            &measurements! {
                root_id: root.as_u32() as u64,
                revision: revision,
                executable_count: program.executables.len() as u64,
                callable_entry_count: program.callable_entries.len() as u64,
            },
            &metadata! {
                program: opaque(&program),
            },
        );
        revision
    }

    pub fn reference_module(&mut self, name: impl Into<String>) -> ModuleId {
        self.modules.reference_named(name)
    }

    pub fn reference_child_module(&mut self, parent: ModuleId, local_name: &str) -> ModuleId {
        let name = self.qualified_module_name(parent, local_name);
        self.modules.reference_named(name)
    }

    pub fn define_module(&mut self, id: ModuleId, namespace: Namespace, exports: Vec<ModuleExport>) -> u64 {
        let code = self.module_definition_code(id);
        let revision = self.modules.define(id, code, namespace, exports);
        let module = self.modules.get(id);
        self.tel.execute(
            &["fz", "compiler2", "module", "defined"],
            &measurements! {
                code_id: code.as_u32() as u64,
                module_id: id.as_u32() as u64,
                revision: revision,
            },
            &metadata! {
                module: opaque(module),
            },
        );
        revision
    }

    pub fn index_module_body(
        &mut self,
        id: ModuleId,
        code: CodeId,
        parent: ModuleId,
        local_name: String,
        attrs: Vec<crate::ast::Attribute>,
        items: Vec<Rc<Item>>,
    ) -> u64 {
        self.modules.index_body(id, code, parent, local_name, attrs, items)
    }

    pub fn index_protocol_module(
        &mut self,
        id: ModuleId,
        code: CodeId,
        parent: ModuleId,
        local_name: String,
        attrs: Vec<crate::ast::Attribute>,
        callbacks: Vec<crate::ast::ProtocolCallback>,
    ) -> u64 {
        self.modules
            .index_protocol(id, code, parent, local_name, attrs, callbacks)
    }

    pub fn scope_module(&mut self, id: ModuleId, base_namespace: Namespace) -> u64 {
        self.modules.scope(id, base_namespace)
    }

    pub fn reference_function(&mut self, module: ModuleId, name: impl Into<String>, arity: usize) -> FunctionId {
        self.functions.reference(module, name, arity)
    }

    pub fn define_function(
        &mut self,
        module: ModuleId,
        owner_module: ModuleId,
        local_name: String,
        code: CodeId,
        namespace: Namespace,
        ast: FnDef,
    ) -> (FunctionId, u64) {
        let arity = ast.arity();
        let clauses = ast.clauses.len() as u64;
        let id = self.functions.reference(module, local_name, arity);
        let previous_revision = self.functions.get(id).revision;
        let revision = self.functions.define(
            id,
            FunctionDef {
                code,
                owner_module,
                namespace,
                capture_params: Vec::new(),
                ast,
            },
        );
        if revision != previous_revision {
            let function = self.functions.get(id);
            let function_ref = self.functions.reference_for(id);
            self.tel.execute(
                &["fz", "compiler2", "function", "defined"],
                &measurements! {
                    code_id: code.as_u32() as u64,
                    module_id: module.as_u32() as u64,
                    owner_module_id: owner_module.as_u32() as u64,
                    function_id: id.as_u32() as u64,
                    revision: revision,
                    arity: arity as u64,
                    clauses: clauses,
                },
                &metadata! {
                    function: opaque(function),
                    function_ref: opaque(function_ref),
                },
            );
        }
        (id, revision)
    }

    pub(crate) fn define_protocol_callback(&mut self, function: FunctionId, protocol: ModuleId) -> u64 {
        let callback = ProtocolCallback { protocol };
        let revision = self.protocol_callbacks.define(function, callback);
        let function_ref = self.functions.reference_for(function);
        self.tel.execute(
            &["fz", "compiler2", "protocol_callback", "defined"],
            &measurements! {
                protocol_id: protocol.as_u32() as u64,
                function_id: function.as_u32() as u64,
                revision: revision,
                arity: function_ref.arity as u64,
            },
            &metadata! {
                callback: opaque(&callback),
                function_ref: opaque(function_ref),
            },
        );
        revision
    }

    pub(crate) fn protocol_callback(&self, function: FunctionId) -> Option<ProtocolCallback> {
        self.protocol_callbacks
            .get(function)
            .or_else(|| self.derived_protocol_callback(function))
    }

    pub(crate) fn define_protocol_impl(
        &mut self,
        protocol: ModuleId,
        target: ModuleId,
        callbacks: HashMap<(String, usize), ProtocolCallbackImpl>,
    ) -> u64 {
        let key = ProtocolImplKey { protocol, target };
        let protocol_impl = ProtocolImpl { callbacks };
        let revision = self.protocol_impls.define(key, protocol_impl.clone());
        self.tel.execute(
            &["fz", "compiler2", "protocol_impl", "defined"],
            &measurements! {
                protocol_id: protocol.as_u32() as u64,
                target_id: target.as_u32() as u64,
                revision: revision,
                callbacks: protocol_impl.callbacks.len() as u64,
            },
            &metadata! {
                key: opaque(&key),
                protocol_impl: opaque(&protocol_impl),
            },
        );
        revision
    }

    pub(crate) fn protocol_impl(&self, protocol: ModuleId, target: ModuleId) -> Option<&ProtocolImpl> {
        self.protocol_impls.impl_for(&ProtocolImplKey { protocol, target })
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
        ast: FnDef,
    ) -> (FunctionId, u64) {
        let owner_def = self.function_definition(owner);
        let owner_module = self.functions.reference_for(owner).module;
        let owner_code = owner_def.code;
        let id = self
            .functions
            .reference_generated(owner, owner_module, ast.span, ast.arity());
        let previous_revision = self.functions.get(id).revision;
        let revision = self.functions.define(
            id,
            super::identity::FunctionDef {
                code: owner_code,
                owner_module: owner_def.owner_module,
                namespace,
                capture_params,
                ast: ast.clone(),
            },
        );
        if revision != previous_revision {
            let function = self.functions.get(id);
            let function_ref = self.functions.reference_for(id);
            self.tel.execute(
                &["fz", "compiler2", "function", "defined"],
                &measurements! {
                    code_id: owner_code.as_u32() as u64,
                    module_id: owner_module.as_u32() as u64,
                    owner_module_id: owner_def.owner_module.as_u32() as u64,
                    function_id: id.as_u32() as u64,
                    revision: revision,
                    arity: ast.arity() as u64,
                    clauses: ast.clauses.len() as u64,
                    owner_function_id: owner.as_u32() as u64,
                },
                &metadata! {
                    function: opaque(function),
                    function_ref: opaque(function_ref),
                },
            );
        }
        (id, revision)
    }

    pub(crate) fn define_lowered_body(&mut self, function: FunctionId, body: LoweredBody) -> u64 {
        let revision = self.bodies.define(function, body.clone());
        let function_ref = self.functions.reference_for(function);
        let slot = self.functions.get(function);
        let def = match &slot.state {
            super::identity::FunctionState::Defined { def } => def.as_ref(),
            super::identity::FunctionState::Placeholder => {
                panic!("lowered bodies should only be defined for known functions")
            }
        };
        let (clauses, generated, arity) = match &body {
            LoweredBody::Extern { signature } => (0_u64, 0_u64, signature.params.len() as u64),
            LoweredBody::Clauses { clauses, generated } => {
                (clauses.len() as u64, generated.len() as u64, def.ast.arity() as u64)
            }
        };
        self.tel.execute(
            &["fz", "compiler2", "lowered_body", "defined"],
            &measurements! {
                code_id: def.code.as_u32() as u64,
                module_id: function_ref.module.as_u32() as u64,
                function_id: function.as_u32() as u64,
                revision: revision,
                arity: arity,
                clauses: clauses,
                generated: generated,
            },
            &metadata! {
                function_ref: opaque(function_ref),
                body: opaque(&body),
            },
        );
        revision
    }

    pub(crate) fn define_guard_dispatch(&mut self, function: FunctionId, dispatch: PatternGuardDispatch<Ty>) -> u64 {
        let revision = self.guard_dispatches.define(function, dispatch.clone());
        let function_ref = self.functions.reference_for(function);
        let slot = self.functions.get(function);
        let def = match &slot.state {
            super::identity::FunctionState::Defined { def } => def.as_ref(),
            super::identity::FunctionState::Placeholder => {
                panic!("guard dispatch should only be defined for known functions")
            }
        };
        self.tel.execute(
            &["fz", "compiler2", "guard_dispatch", "defined"],
            &measurements! {
                code_id: def.code.as_u32() as u64,
                module_id: function_ref.module.as_u32() as u64,
                function_id: function.as_u32() as u64,
                revision: revision,
                arity: def.ast.arity() as u64,
                bodies: dispatch.bodies.len() as u64,
                guards: dispatch.plan.guards.len() as u64,
                pinned: dispatch.plan.pinned.len() as u64,
            },
            &metadata! {
                function_ref: opaque(function_ref),
                dispatch: opaque(&dispatch),
            },
        );
        revision
    }

    pub(crate) fn define_entry_dispatch(&mut self, function: FunctionId, plan: PatternDispatchPlan<Ty>) -> u64 {
        let revision = self.entry_dispatches.define(function, plan.clone());
        let function_ref = self.functions.reference_for(function);
        let slot = self.functions.get(function);
        let def = match &slot.state {
            super::identity::FunctionState::Defined { def } => def.as_ref(),
            super::identity::FunctionState::Placeholder => {
                panic!("entry dispatch should only be defined for known functions")
            }
        };
        self.tel.execute(
            &["fz", "compiler2", "entry_dispatch", "defined"],
            &measurements! {
                code_id: def.code.as_u32() as u64,
                module_id: function_ref.module.as_u32() as u64,
                function_id: function.as_u32() as u64,
                revision: revision,
                arity: def.ast.arity() as u64,
                outcomes: plan.outcomes.len() as u64,
                guards: plan.guards.len() as u64,
                pinned: plan.pinned.len() as u64,
            },
            &metadata! {
                function_ref: opaque(function_ref),
                plan: opaque(&plan),
            },
        );
        revision
    }

    pub(crate) fn define_recursive(&mut self, function: FunctionId, recursive: bool) -> u64 {
        self.recursive.define(function, recursive)
    }

    pub(crate) fn define_dispatch_mask(&mut self, function: FunctionId, mask: Vec<bool>) -> u64 {
        self.dispatch_masks.define(function, mask)
    }

    pub(crate) fn entry_dispatch(&self, function: FunctionId) -> PatternDispatchPlan<Ty> {
        self.entry_dispatches
            .get(function)
            .cloned()
            .expect("entry dispatch should only be read after its fact is defined")
    }

    pub(crate) fn lowered_body(&self, function: FunctionId) -> LoweredBody {
        match &self
            .bodies
            .get(function)
            .expect("body slots should exist before reading lowered bodies")
            .state
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

    pub(crate) fn runtime_prelude(&self) -> CodeId {
        self.runtime_prelude
    }

    pub(crate) fn is_runtime_prelude(&self, code: CodeId) -> bool {
        code == self.runtime_prelude
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

    pub fn module_exports(&self, module: ModuleId) -> Vec<ModuleExport> {
        match &self.modules.get(module).state {
            ModuleState::Defined { surface, .. } => surface.exports.clone(),
            ModuleState::Placeholder | ModuleState::Indexed(_) | ModuleState::Scoped { .. } => {
                panic!("module exports should only be read from defined modules")
            }
        }
    }

    pub(crate) fn module_name(&self, module: ModuleId) -> Option<&str> {
        self.modules.name(module)
    }

    pub fn finish_code_index(&mut self, id: CodeId, items: Vec<Rc<Item>>) -> u64 {
        self.code.index(id, items)
    }

    pub fn code_revision(&self, id: CodeId) -> u64 {
        self.code.get(id).revision
    }

    pub fn module_defined_revision(&self, module: ModuleId) -> Option<u64> {
        if !matches!(&self.modules.get(module).state, ModuleState::Defined { .. }) {
            return None;
        }
        self.work_graph.facts().revision(&FactKey::ModuleDefined(module))
    }

    pub fn function_defined_revision(&self, function: FunctionId) -> Option<u64> {
        if !matches!(
            self.functions.get(function).state,
            super::identity::FunctionState::Defined { .. }
        ) {
            return None;
        }
        self.work_graph.facts().revision(&FactKey::FunctionDefined(function))
    }

    pub(crate) fn function_definition(&self, function: FunctionId) -> super::identity::FunctionDef {
        match &self.functions.get(function).state {
            super::identity::FunctionState::Defined { def } => def.as_ref().clone(),
            super::identity::FunctionState::Placeholder => {
                panic!("function definitions should only be read from defined functions")
            }
        }
    }

    pub(crate) fn function_module(&self, function: FunctionId) -> ModuleId {
        self.functions.reference_for(function).module
    }

    pub(crate) fn function_ref(&self, function: FunctionId) -> &super::identity::FunctionRef {
        self.functions.reference_for(function)
    }

    pub(crate) fn function_arity(&self, function: FunctionId) -> usize {
        self.functions.reference_for(function).arity
    }

    pub(crate) fn function_variadic(&self, function: FunctionId) -> bool {
        match &self.functions.get(function).state {
            super::identity::FunctionState::Defined { def } => def.ast.variadic,
            super::identity::FunctionState::Placeholder => false,
        }
    }

    pub(crate) fn ensure_function_surface(&mut self, function: FunctionId) -> Vec<Job> {
        let module = self.function_module(function);
        if module.is_global() {
            return Vec::new();
        }
        self.ensure_runtime_module(module);
        vec![Job::DefineModule(module)]
    }

    pub(crate) fn wait_for_function_definition(&mut self, function: FunctionId) -> JobEffects {
        JobEffects::wait_on(
            FactKey::FunctionDefined(function),
            self.ensure_function_surface(function),
        )
    }

    pub fn fact_revision(&self, key: FactKey) -> Option<u64> {
        self.work_graph.facts().revision(&key)
    }

    pub(crate) fn require_activation_key_facts(
        &self,
        function: FunctionId,
        reads: &mut Vec<FactKey>,
        waits: &mut HashSet<FactKey>,
        follow_up: &mut HashSet<Job>,
    ) -> bool {
        let recursive = FactKey::Recursive(function);
        let recursive_ready = self.fact_revision(recursive.clone()).is_some();
        if recursive_ready {
            reads.push(recursive);
        } else {
            waits.insert(recursive);
            follow_up.insert(Job::DeriveRecursive(function));
        }

        let dispatch_mask = FactKey::DispatchMask(function);
        let dispatch_mask_ready = self.fact_revision(dispatch_mask.clone()).is_some();
        if dispatch_mask_ready {
            reads.push(dispatch_mask);
        } else {
            waits.insert(dispatch_mask);
            follow_up.insert(Job::DeriveDispatchMask(function));
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
                NamespaceSymbol::Function(function) | NamespaceSymbol::Macro(function) => {
                    callable_match_score(self.function_arity(*function), self.function_variadic(*function), arity)
                }
                NamespaceSymbol::Module(_) => None,
            })
            .cloned()
    }

    fn lookup_module_callable(&mut self, module: ModuleId, name: &str, arity: usize) -> Option<NamespaceSymbol> {
        if self.module_defined_revision(module).is_none() {
            return Some(NamespaceSymbol::Function(self.reference_function(
                module,
                name.to_string(),
                arity,
            )));
        }
        let mut best = None;
        for export in self.module_exports(module) {
            if export.name != name {
                continue;
            }
            let Some(score) = callable_match_score(export.arity, export.variadic, arity) else {
                continue;
            };
            let replace = best
                .as_ref()
                .is_none_or(|(current, _): &(CallableMatchScore, NamespaceSymbol)| score > *current);
            if replace {
                best = Some((score, export.symbol));
            }
        }
        best.map(|(_, symbol)| symbol)
    }

    pub(crate) fn min_variadic_arity(&mut self, head: Namespace, name: &str) -> Option<usize> {
        if let Some((module_path, local_name)) = name.rsplit_once('.') {
            let module = self.lookup_module_path(head, module_path)?;
            self.module_defined_revision(module)?;
            return self
                .module_exports(module)
                .into_iter()
                .filter(|export| export.name == local_name && export.variadic)
                .map(|export| export.arity)
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
                NamespaceSymbol::Module(_) => unreachable!("variadic lookup should not yield modules"),
            })
    }

    pub(crate) fn guard_dispatch(&self, function: FunctionId) -> PatternGuardDispatch<Ty> {
        self.guard_dispatches
            .get(function)
            .cloned()
            .expect("guard dispatch should only be read after its fact is defined")
    }

    pub(crate) fn function_type_env(
        &mut self,
        function: FunctionId,
    ) -> Result<ModuleTypeEnv<Ty>, crate::type_expr::TypeExprError> {
        let module = self.function_definition(function).owner_module;
        let builtin_env = builtin_type_env(&mut self.types);
        if module.is_global() {
            return Ok(builtin_env);
        }
        let module_name = self
            .modules
            .name(module)
            .expect("named function modules should have a reverse lookup")
            .to_string();
        let attrs = match &self.modules.get(module).state {
            ModuleState::Indexed(source) | ModuleState::Scoped { source, .. } | ModuleState::Defined { source, .. } => {
                source.attrs.clone()
            }
            ModuleState::Placeholder => {
                panic!("function modules should have source metadata before resolving type env")
            }
        };
        build_module_type_env_for_with_base(&mut self.types, &attrs, &module_name, &builtin_env).map(|(env, _, _)| env)
    }

    pub fn code_items(&self, id: CodeId) -> Option<&[Rc<Item>]> {
        match &self.code.get(id).state {
            super::code::CodeState::Indexed { items } => Some(items.as_slice()),
            super::code::CodeState::Pending => None,
        }
    }

    pub fn module_scope(&self, module: ModuleId) -> Option<(super::identity::ModuleSource, Namespace)> {
        match &self.modules.get(module).state {
            ModuleState::Scoped { source, base } => Some((source.clone(), *base)),
            ModuleState::Defined { source, surface } => Some((source.clone(), surface.base)),
            _ => None,
        }
    }

    pub fn module_indexed_parent(&self, module: ModuleId) -> Option<(CodeId, ModuleId)> {
        match &self.modules.get(module).state {
            ModuleState::Indexed(source) => Some((source.code, source.parent)),
            _ => None,
        }
    }

    fn module_definition_code(&self, module: ModuleId) -> CodeId {
        match &self.modules.get(module).state {
            ModuleState::Scoped { source, .. } | ModuleState::Defined { source, .. } => source.code,
            ModuleState::Placeholder | ModuleState::Indexed(_) => {
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
            .expect("activation keying should wait for dispatch mask facts before activation");
        let recursive = *self
            .recursive
            .get(function)
            .expect("activation keying should wait for recursive facts before activation");
        let canonical = inputs
            .iter()
            .map(|input| self.types.widen_for_recursive_spec_key(input))
            .collect::<Vec<_>>();
        let key_inputs = canonical
            .iter()
            .enumerate()
            .map(|(slot, input)| {
                if recursive && !mask.get(slot).copied().unwrap_or(true) {
                    self.types.convergence_class(input)
                } else {
                    *input
                }
            })
            .collect::<Vec<_>>();
        let key_inputs = key_inputs
            .into_iter()
            .map(|input| self.types.alpha_normalize_vars(&input))
            .collect();
        super::identity::ActivationKey {
            root,
            function,
            input: key_inputs,
        }
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
        let code_id = self.submit_code(Some(source_name), source.to_string());
        self.runtime_modules
            .get_mut(&module)
            .expect("runtime module should still exist while recording its code id")
            .code_id = Some(code_id);
        Some(code_id)
    }

    pub(crate) fn runtime_impl_target_modules(&mut self, receiver_ty: &Ty) -> Vec<ModuleId> {
        let mut modules = Vec::new();
        let runtime_modules = self.runtime_modules.keys().copied().collect::<Vec<_>>();
        for module in runtime_modules {
            let target_ty = self.module_impl_target_ty(module);
            if self.types.is_subtype(receiver_ty, &target_ty) {
                modules.push(module);
            }
        }
        modules.sort_by_key(|module| module.as_u32());
        modules
    }

    pub(crate) fn module_impl_target_ty(&mut self, module: ModuleId) -> Ty {
        self.module_impl_target_ty_with(module)
    }

    fn lookup_module_path(&mut self, head: Namespace, path: &str) -> Option<ModuleId> {
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

    fn module_impl_target_ty_with(&mut self, module: ModuleId) -> Ty {
        let name = self
            .module_name(module)
            .expect("impl target modules should have reverse names")
            .to_string();
        impl_target_ty(&mut self.types, &name)
    }

    fn derived_protocol_callback(&self, function: FunctionId) -> Option<ProtocolCallback> {
        let function_ref = self.functions.reference_for(function);
        let module = self.modules.get(function_ref.module);
        let source = match &module.state {
            ModuleState::Indexed(source) | ModuleState::Scoped { source, .. } | ModuleState::Defined { source, .. } => {
                source
            }
            ModuleState::Placeholder => return None,
        };
        match &source.kind {
            ModuleSourceKind::Protocol { callbacks }
                if callbacks
                    .iter()
                    .any(|callback| callback.name == function_ref.name && callback.arity == function_ref.arity) =>
            {
                Some(ProtocolCallback {
                    protocol: function_ref.module,
                })
            }
            ModuleSourceKind::Body { .. } | ModuleSourceKind::Protocol { .. } => None,
        }
    }

    fn unresolved_issues(&self, waits: &[UnresolvedWait<Job, FactKey>]) -> Vec<UnresolvedIssue> {
        let frontier = waits.iter().map(|wait| wait.fact.clone()).collect::<HashSet<_>>();
        let mut issues = Vec::new();
        for wait in waits {
            if let Some(issue) = self.unresolved_issue(&frontier, &wait.fact) {
                issues.push(issue);
            }
        }
        issues.sort_by_key(|issue| match issue.key {
            UnresolvedIssueKey::Module(module) => (0_u8, module.as_u32()),
            UnresolvedIssueKey::Function(function) => (1_u8, function.as_u32()),
            UnresolvedIssueKey::Export(function) => (2_u8, function.as_u32()),
        });
        issues.dedup_by_key(|issue| issue.key);
        issues
    }

    fn unresolved_issue(&self, frontier: &HashSet<FactKey>, fact: &FactKey) -> Option<UnresolvedIssue> {
        match fact {
            FactKey::ModuleIndexed(module) => Some(UnresolvedIssue {
                key: UnresolvedIssueKey::Module(*module),
                diagnostic: Diagnostic::error(
                    codes::RESOLVE_UNKNOWN_MODULE,
                    format!(
                        "module `{}` is not defined",
                        self.module_name(*module)
                            .expect("referenced modules should have reverse names")
                    ),
                    Span::DUMMY,
                ),
            }),
            FactKey::FunctionDefined(function) => self.unresolved_function_issue(frontier, *function),
            _ => None,
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

fn callable_match_score(fixed_arity: usize, variadic: bool, actual_arity: usize) -> Option<CallableMatchScore> {
    if fixed_arity == actual_arity {
        return Some(CallableMatchScore::Exact);
    }
    if variadic && fixed_arity <= actual_arity {
        return Some(CallableMatchScore::VariadicPrefix(fixed_arity));
    }
    None
}

fn impl_target_ty<T: crate::types::Types<Ty = Ty>>(t: &mut T, module_name: &str) -> Ty {
    match module_name.rsplit('.').next().unwrap_or(module_name) {
        "List" => {
            let any = t.any();
            t.list(any)
        }
        "Integer" => t.int(),
        "Float" => t.float(),
        "Atom" => t.atom(),
        "Binary" => t.str_t(),
        "Map" => t.map_top(),
        other => crate::frontend::protocols::struct_impl_target_type(t, other),
    }
}
