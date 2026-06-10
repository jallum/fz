//! Compiler2's owned world state.
//!
//! Compiler-owned identities are total here. A `CodeId`, `ModuleId`,
//! `FunctionId`, or `RootId` that came from Compiler2 must resolve; a bad id is
//! a bug and should panic at the lookup boundary. `Option` is reserved for
//! legitimate state absence like "this known function is still a placeholder"
//! or "this known code has not been indexed yet".

use std::cmp::Reverse;
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::compiler::source::Span;
use crate::diag::driver::emit_through;
use crate::diag::{Diagnostic, codes};
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardDispatch};
use crate::frontend::protocols::{
    ImplTarget as InterfaceImplTarget, PROTOCOL_ELEM_VAR, impl_target_type_with_element, protocol_domain_tag,
};
use crate::modules::runtime_library;
use crate::telemetry::{Telemetry, opaque_debug};
use crate::{FunctionSurface, measurements, metadata};

use super::CodeId;
use super::artifact::{
    AbiReadyProgram, AbiReadyProgramMap, BackendProgram, BackendProgramMap, EmissionReadyProgram,
    EmissionReadyProgramMap, MaterializedProgram, MaterializedProgramMap, NativeProgram, NativeProgramMap,
};
use super::body::{LoweredBody, LoweredBodyMap};
use super::code::{CodeMap, QuotedCodeSource};
use super::contract::{FunctionContract, FunctionContractMap};
use super::deps::UnresolvedWait;
use super::dispatch::{EntryDispatchMap, GuardDispatchMap};
use super::drive::{FactKey, Job, JobEffects, WorkGraph};
use super::facts::FactValue;
use super::identity::{
    ActivationKey, ExecutableNeed, FunctionDef, FunctionId, FunctionMap, FunctionSource, FunctionSourceMap,
    FunctionSourceState, ModuleExport, ModuleId, ModuleMap, ModuleSourceKind, ModuleState, NotedTypeDecl, RootEntry,
    RootId, RootMap, TypeDeclMap, TypeName, TypeRefMap,
};
use super::keying::{DispatchMaskMap, RecursiveMap};
use super::namespace::{Namespace, NamespaceStore, NamespaceSymbol};
use super::protocol::{
    ProtocolCallback, ProtocolCallbackImpl, ProtocolCallbackMap, ProtocolDispatch, ProtocolDispatchArm,
    ProtocolDispatchMap, ProtocolImpl, ProtocolImplKey, ProtocolImplMap,
};
use super::runtime::{self, RuntimeModuleCode};
use super::scope::ScopeSnapshot;
use super::semantic::{
    ActivationAnalysis, ActivationMap, CallSiteKey, CallSiteMap, CallSiteSummary, SemanticClosure, SemanticClosureMap,
};
use super::source::QuotedSourceRoot;
#[cfg(test)]
use super::source::{
    QuotedLexicalContext, QuotedLexicalContextKind, QuotedSourceBuilder, QuotedSourceError, QuotedSourceMetadata,
};
use super::typedef::{TypeDef, TypeDefMap};
use super::types::{ClosureTarget, Ty, Types};
#[cfg(test)]
use fz_runtime::any_value::AnyValueRef;

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
    function_sources: FunctionSourceMap,
    type_decls: TypeDeclMap,
    type_refs: TypeRefMap,
    type_defs: TypeDefMap,
    function_contracts: FunctionContractMap,
    bodies: LoweredBodyMap,
    guard_dispatches: GuardDispatchMap,
    entry_dispatches: EntryDispatchMap,
    recursive: RecursiveMap,
    dispatch_masks: DispatchMaskMap,
    protocol_callbacks: ProtocolCallbackMap,
    protocol_impls: ProtocolImplMap,
    protocol_dispatches: ProtocolDispatchMap,
    activations: ActivationMap,
    callsites: CallSiteMap,
    semantic_closures: SemanticClosureMap,
    artifacts: MaterializedProgramMap,
    abi_ready: AbiReadyProgramMap,
    emission_ready: EmissionReadyProgramMap,
    backend: BackendProgramMap,
    native: NativeProgramMap,
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
            .field("function_sources", &self.function_sources)
            .field("function_contracts", &self.function_contracts)
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
            function_sources: FunctionSourceMap::new(),
            type_decls: TypeDeclMap::new(),
            type_refs: TypeRefMap::new(),
            type_defs: TypeDefMap::new(),
            function_contracts: FunctionContractMap::new(),
            bodies: LoweredBodyMap::new(),
            guard_dispatches: GuardDispatchMap::new(),
            entry_dispatches: EntryDispatchMap::new(),
            recursive: RecursiveMap::new(),
            dispatch_masks: DispatchMaskMap::new(),
            protocol_callbacks: ProtocolCallbackMap::new(),
            protocol_impls: ProtocolImplMap::new(),
            protocol_dispatches: ProtocolDispatchMap::new(),
            activations: ActivationMap::new(),
            callsites: CallSiteMap::new(),
            semantic_closures: SemanticClosureMap::new(),
            artifacts: MaterializedProgramMap::new(),
            abi_ready: AbiReadyProgramMap::new(),
            emission_ready: EmissionReadyProgramMap::new(),
            backend: BackendProgramMap::new(),
            native: NativeProgramMap::new(),
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
                root: opaque_debug(root),
                function_ref: opaque_debug(function_ref),
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
                job: opaque_debug(&job),
                step: opaque_debug(&step),
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
                activation: opaque_debug(key),
                analysis: opaque_debug(&analysis),
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
                activation: opaque_debug(key),
                return_ty: opaque_debug(&return_ty),
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
                callsite: opaque_debug(&key),
                summary: opaque_debug(&summary),
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
                closure: opaque_debug(&closure),
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
                program: opaque_debug(&program),
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
                program: opaque_debug(&program),
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
                program: opaque_debug(&program),
            },
        );
        revision
    }

    pub(crate) fn emission_ready_program(&self, root: RootId) -> EmissionReadyProgram {
        self.emission_ready
            .get(root)
            .cloned()
            .expect("emission-ready programs should only be read after their fact is defined")
    }

    pub(crate) fn define_backend_program(&mut self, root: RootId, program: BackendProgram) -> u64 {
        let revision = self.backend.define(root, program.clone());
        self.tel.execute(
            &["fz", "compiler2", "backend_program", "defined"],
            &measurements! {
                root_id: root.as_u32() as u64,
                revision: revision,
                atom_count: program.atom_names.len() as u64,
                executable_count: program.executables.len() as u64,
                callable_entry_count: program.callable_entries.len() as u64,
            },
            &metadata! {
                program: opaque_debug(&program),
            },
        );
        revision
    }

    pub(crate) fn backend_program(&self, root: RootId) -> BackendProgram {
        self.backend
            .get(root)
            .cloned()
            .expect("backend programs should only be read after their fact is defined")
    }

    pub(crate) fn define_native_program(&mut self, root: RootId, program: NativeProgram) -> u64 {
        let revision = self.native.define(root, program.clone());
        self.tel.execute(
            &["fz", "compiler2", "native_program", "defined"],
            &measurements! {
                root_id: root.as_u32() as u64,
                revision: revision,
                body_count: program.bodies.len() as u64,
                callable_entry_count: program.callable_entries.len() as u64,
                fn_count: program.module.fns.len() as u64,
            },
            &metadata! {
                program: opaque_debug(&program),
            },
        );
        revision
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
                module: opaque_debug(module),
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
        source: QuotedSourceRoot,
        surface: super::quoted_surface::ScopeSurface,
    ) -> u64 {
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
    ) -> u64 {
        self.modules
            .index_protocol(id, code, parent, local_name, source, surface)
    }

    pub fn scope_module(&mut self, id: ModuleId, base_namespace: Namespace) -> u64 {
        self.modules.scope(id, base_namespace)
    }

    pub fn reference_function(&mut self, module: ModuleId, name: impl Into<String>, arity: usize) -> FunctionId {
        self.functions.reference(module, name, arity)
    }

    /// Holds a `@type` declaration's unresolved decl — parsed body plus the
    /// namespace captured at its scope — under its identity, for
    /// `DeriveTypeDef` to read. No resolution, no type-algebra. The event is
    /// the surface-tier signal that a type name became a referenceable identity.
    pub fn note_type_decl(&mut self, name: TypeName, decl: NotedTypeDecl) {
        self.tel.execute(
            &["fz", "compiler2", "type", "noted"],
            &measurements! {
                module_id: name.module.as_u32() as u64,
                arity: name.arity as u64,
                namespace: decl.namespace.as_u32() as u64,
            },
            &metadata! {
                name: name.name.clone(),
                kind: format!("{:?}", decl.body.kind),
            },
        );
        self.type_decls.note(name, decl);
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
        let consumer = format!("fn:{}", self.functions.reference_for(function).name);
        for referenced in &refs {
            self.emit_type_referenced(&consumer, referenced);
        }
        self.type_refs.record_function(function, refs);
    }

    // Consumed by the contract re-seat (fz-rh2.12.4); recorded one inch ahead.
    #[allow(dead_code)]
    pub(crate) fn function_type_refs(&self, function: FunctionId) -> &[TypeName] {
        self.type_refs.function_refs(function)
    }

    /// Records the type names a `@type` body references — the wait-set
    /// `DeriveTypeDef` resolves against before minting the symbol (fz-rh2.12.2).
    pub(crate) fn record_type_def_refs(&mut self, name: TypeName, mut refs: Vec<TypeName>) {
        dedup_type_names(&mut refs);
        let consumer = format!("type:{}", name.name);
        for referenced in &refs {
            self.emit_type_referenced(&consumer, referenced);
        }
        self.type_refs.record_type(name, refs);
    }

    /// The type names a `@type` body references — `DeriveTypeDef`'s wait-set.
    pub(crate) fn type_def_refs(&self, name: &TypeName) -> &[TypeName] {
        self.type_refs.type_refs(name)
    }

    /// Publishes a resolved type definition under `name` and emits the
    /// callee-tier `type defined` signal. The rendered type rides the event so
    /// tests and tooling can read the resolved surface without the interner.
    pub(crate) fn define_type_def(&mut self, name: TypeName, def: TypeDef) -> u64 {
        let rendered = self.types.display(&def.ty);
        let has_vars = self.types.has_vars(&def.ty);
        let params = def.params.len();
        let revision = self.type_defs.define(name.clone(), def);
        self.tel.execute(
            &["fz", "compiler2", "type", "defined"],
            &measurements! {
                module_id: name.module.as_u32() as u64,
                arity: name.arity as u64,
                params: params as u64,
                revision: revision,
                has_vars: has_vars as u64,
            },
            &metadata! {
                name: name.name.clone(),
                ty: rendered,
            },
        );
        revision
    }

    pub(crate) fn type_def(&self, name: &TypeName) -> Option<&TypeDef> {
        self.type_defs.get(name)
    }

    pub(crate) fn refresh_protocol_domain_facts(&mut self, protocol: ModuleId) -> Vec<(FactKey, FactValue)> {
        let mut outputs = Vec::new();
        for name in [
            protocol_domain_type_name(protocol, 0),
            protocol_domain_type_name(protocol, 1),
        ] {
            let Some(def) = self.protocol_domain_type_def(&name) else {
                continue;
            };
            let revision = self.define_type_def(name.clone(), def);
            outputs.push((FactKey::TypeDefined(name), FactValue::presence(revision)));
        }
        outputs
    }

    pub(crate) fn protocol_domain_type_def(&mut self, name: &TypeName) -> Option<TypeDef> {
        if !self.is_protocol_domain_type(name) {
            return None;
        }
        let protocol = self
            .module_name(name.module)
            .and_then(|path| crate::modules::identity::ModuleName::parse_dotted(path).ok())?;
        let (ty, params) = match name.arity {
            0 => {
                let any = self.types.any();
                let mut domain = self.types.opaque_of(&protocol_domain_tag(&protocol));
                for (key, _protocol_impl) in self.protocol_impls_for(name.module) {
                    let target_name = self
                        .module_name(key.target)
                        .and_then(|path| crate::modules::identity::ModuleName::parse_dotted(path).ok())?;
                    let target_ty =
                        impl_target_type_with_element(&mut self.types, &InterfaceImplTarget::module(target_name), any);
                    domain = self.types.union(domain, target_ty);
                }
                (domain, Vec::new())
            }
            1 => {
                let element = self.types.type_var(PROTOCOL_ELEM_VAR);
                let mut domain = self.types.opaque_of(&protocol_domain_tag(&protocol));
                for (key, _protocol_impl) in self.protocol_impls_for(name.module) {
                    let target_name = self
                        .module_name(key.target)
                        .and_then(|path| crate::modules::identity::ModuleName::parse_dotted(path).ok())?;
                    let target_ty = impl_target_type_with_element(
                        &mut self.types,
                        &InterfaceImplTarget::module(target_name),
                        element,
                    );
                    domain = self.types.union(domain, target_ty);
                }
                (domain, vec![PROTOCOL_ELEM_VAR])
            }
            _ => return None,
        };
        Some(TypeDef { ty, params })
    }

    pub(crate) fn define_protocol_dispatch(&mut self, protocol: ModuleId, dispatch: ProtocolDispatch) -> u64 {
        let revision = self.protocol_dispatches.define(protocol, dispatch.clone());
        self.tel.execute(
            &["fz", "compiler2", "protocol_dispatch", "defined"],
            &measurements! {
                protocol_id: protocol.as_u32() as u64,
                revision: revision,
                arms: dispatch.arms.len() as u64,
            },
            &metadata! {
                dispatch: opaque_debug(&dispatch),
            },
        );
        revision
    }

    pub(crate) fn refresh_protocol_dispatch_fact(&mut self, protocol: ModuleId) -> (FactKey, FactValue) {
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
        let revision = self.define_protocol_dispatch(protocol, dispatch);
        (FactKey::ProtocolDispatch(protocol), FactValue::presence(revision))
    }

    pub(crate) fn protocol_dispatch(&self, protocol: ModuleId) -> Option<&ProtocolDispatch> {
        self.protocol_dispatches.get(protocol)
    }

    fn is_protocol_domain_type(&self, name: &TypeName) -> bool {
        name.name == "t"
            && matches!(name.arity, 0 | 1)
            && matches!(
                &self.modules.get(name.module).state,
                ModuleState::Indexed(source) | ModuleState::Scoped { source, .. } | ModuleState::Defined { source, .. }
                    if matches!(source.kind, ModuleSourceKind::Protocol(_))
            )
    }

    /// The qualified tag a nominal `@type` (`refines` / `opaque`) brands under.
    /// A top-level type owns no module, so its tag is its bare name; a module
    /// type is tagged `Module.Path::name`.
    pub(crate) fn qualified_type_tag(&self, name: &TypeName) -> String {
        if self.is_protocol_domain_type(name)
            && let Some(protocol) = self
                .module_name(name.module)
                .and_then(|path| crate::modules::identity::ModuleName::parse_dotted(path).ok())
        {
            return protocol_domain_tag(&protocol);
        }
        if name.module.is_global() {
            return name.name.clone();
        }
        match self.module_name(name.module) {
            Some(path) if !path.is_empty() => format!("{}::{}", path, name.name),
            _ => name.name.clone(),
        }
    }

    fn emit_type_referenced(&self, consumer: &str, referenced: &TypeName) {
        self.tel.execute(
            &["fz", "compiler2", "type", "referenced"],
            &measurements! {
                ref_module_id: referenced.module.as_u32() as u64,
                ref_arity: referenced.arity as u64,
            },
            &metadata! {
                ref_name: referenced.name.clone(),
                consumer: consumer.to_string(),
            },
        );
    }

    pub(crate) fn define_function(
        &mut self,
        module: ModuleId,
        owner_module: ModuleId,
        local_name: String,
        code: CodeId,
        namespace: Namespace,
        source: QuotedSourceRoot,
        surface: FunctionSurface,
    ) -> (FunctionId, u64) {
        let arity = surface.arity();
        let clauses = surface.clauses.len() as u64;
        let id = self.functions.reference(module, local_name, arity);
        let previous_revision = self.functions.get(id).revision;
        let revision = self.functions.define(
            id,
            FunctionDef {
                code,
                owner_module,
                namespace,
                capture_params: Vec::new(),
                source,
                surface,
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
                    source_heap_id: function.state_source_heap_id().unwrap_or_default() as u64,
                    source_root_ref: function.state_source_root_word().unwrap_or_default(),
                },
                &metadata! {
                    function: opaque_debug(function),
                    function_ref: opaque_debug(function_ref),
                },
            );
        }
        (id, revision)
    }

    pub(crate) fn note_function_source(&mut self, function: FunctionId, source: FunctionSource) -> u64 {
        let revision = self.function_sources.note(function, source.clone());
        let function_ref = self.functions.reference_for(function);
        self.tel.execute(
            &["fz", "compiler2", "function", "source", "noted"],
            &measurements! {
                code_id: source.code.as_u32() as u64,
                module_id: function_ref.module.as_u32() as u64,
                owner_module_id: source.owner_module.as_u32() as u64,
                function_id: function.as_u32() as u64,
                revision: revision,
                arity: function_ref.arity as u64,
                clauses: function_source_clause_count(&source),
                source_heap_id: source.source.key().heap_id as u64,
                source_root_ref: source.source.root().raw_word(),
            },
            &metadata! {
                function_ref: opaque_debug(function_ref),
                source: opaque_debug(&source),
            },
        );
        revision
    }

    pub(crate) fn function_source(&self, function: FunctionId) -> Option<FunctionSource> {
        match self.function_sources.get(function)?.state.clone() {
            FunctionSourceState::Placeholder => None,
            FunctionSourceState::Noted { source } => Some(*source),
        }
    }

    pub(crate) fn define_function_contract(&mut self, function: FunctionId, contract: FunctionContract) -> u64 {
        let revision = self.function_contracts.define(function, contract.clone());
        let function_ref = self.functions.reference_for(function);
        self.tel.execute(
            &["fz", "compiler2", "function_contract", "defined"],
            &measurements! {
                function_id: function.as_u32() as u64,
                revision: revision,
                arity: function_ref.arity as u64,
            },
            &metadata! {
                function_ref: opaque_debug(function_ref),
                contract: opaque_debug(&contract),
            },
        );
        revision
    }

    pub(crate) fn function_contract(&self, function: FunctionId) -> Option<&FunctionContract> {
        self.function_contracts.get(function)
    }

    pub(crate) fn function_declares_contract(&self, function: FunctionId) -> bool {
        match &self.functions.get(function).state {
            super::identity::FunctionState::Defined { def } => {
                def.surface.extern_abi.is_some()
                    || def
                        .surface
                        .attrs
                        .iter()
                        .any(|attr| matches!(attr, crate::ast::Attribute::Spec(_)))
            }
            super::identity::FunctionState::Placeholder => false,
        }
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
                callback: opaque_debug(&callback),
                function_ref: opaque_debug(function_ref),
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
                key: opaque_debug(&key),
                protocol_impl: opaque_debug(&protocol_impl),
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
        surface: FunctionSurface,
    ) -> (FunctionId, u64) {
        let owner_def = self.function_definition(owner);
        let owner_module = self.functions.reference_for(owner).module;
        let owner_code = owner_def.code;
        let id = self
            .functions
            .reference_generated(owner, owner_module, surface.span, surface.arity());
        let previous_revision = self.functions.get(id).revision;
        let revision = self.functions.define(
            id,
            super::identity::FunctionDef {
                code: owner_code,
                owner_module: owner_def.owner_module,
                namespace,
                capture_params,
                source: owner_def.source.clone(),
                surface: surface.clone(),
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
                    arity: surface.arity() as u64,
                    clauses: surface.clauses.len() as u64,
                    owner_function_id: owner.as_u32() as u64,
                    source_heap_id: function.state_source_heap_id().unwrap_or_default() as u64,
                    source_root_ref: function.state_source_root_word().unwrap_or_default(),
                },
                &metadata! {
                    function: opaque_debug(function),
                    function_ref: opaque_debug(function_ref),
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
            LoweredBody::Clauses { clauses, generated, .. } => {
                (clauses.len() as u64, generated.len() as u64, def.surface.arity() as u64)
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
                source_root_ref: def.source.root().raw_word(),
            },
            &metadata! {
                function_ref: opaque_debug(function_ref),
                body: opaque_debug(&body),
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
                arity: def.surface.arity() as u64,
                bodies: dispatch.bodies.len() as u64,
                guards: dispatch.plan.guards.len() as u64,
                pinned: dispatch.plan.pinned.len() as u64,
                source_root_ref: def.source.root().raw_word(),
            },
            &metadata! {
                function_ref: opaque_debug(function_ref),
                dispatch: opaque_debug(&dispatch),
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
                arity: def.surface.arity() as u64,
                outcomes: plan.outcomes.len() as u64,
                guards: plan.guards.len() as u64,
                pinned: plan.pinned.len() as u64,
                source_root_ref: def.source.root().raw_word(),
            },
            &metadata! {
                function_ref: opaque_debug(function_ref),
                plan: opaque_debug(&plan),
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

    pub(crate) fn module_struct_fields(&self, module: ModuleId) -> Option<&[String]> {
        match &self.modules.get(module).state {
            ModuleState::Placeholder => None,
            ModuleState::Indexed(source) | ModuleState::Scoped { source, .. } | ModuleState::Defined { source, .. } => {
                match &source.kind {
                    ModuleSourceKind::Protocol(_) => None,
                    ModuleSourceKind::Body(body) => body.forms.iter().find_map(|form| match form {
                        super::quoted_surface::ScopeForm::Struct(def) => Some(def.fields.as_slice()),
                        _ => None,
                    }),
                }
            }
        }
    }

    pub(crate) fn module_name(&self, module: ModuleId) -> Option<&str> {
        self.modules.name(module)
    }

    pub(crate) fn struct_schemas(&self) -> BTreeMap<String, Vec<String>> {
        self.modules.named_struct_schemas()
    }

    pub fn finish_code_index(&mut self, id: CodeId, source: QuotedCodeSource) -> u64 {
        self.code.index(id, source)
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

    pub(crate) fn function_contract_revision(&self, function: FunctionId) -> Option<u64> {
        self.work_graph.facts().revision(&FactKey::FunctionContract(function))
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

    #[cfg(test)]
    pub(crate) fn function_scope(&self, function: FunctionId) -> Option<ScopeSnapshot> {
        match &self.functions.get(function).state {
            super::identity::FunctionState::Defined { def } => {
                Some(ScopeSnapshot::function(def.owner_module, def.namespace, function))
            }
            super::identity::FunctionState::Placeholder => self
                .function_source(function)
                .map(|source| ScopeSnapshot::function(source.owner_module, source.namespace, function)),
        }
    }

    pub(crate) fn function_arity(&self, function: FunctionId) -> usize {
        self.functions.reference_for(function).arity
    }

    pub(crate) fn function_variadic(&self, function: FunctionId) -> bool {
        match &self.functions.get(function).state {
            super::identity::FunctionState::Defined { def } => def.surface.variadic,
            super::identity::FunctionState::Placeholder => {
                self.function_source(function).is_some_and(|source| source.variadic)
            }
        }
    }

    pub(crate) fn ensure_function_source(&mut self, function: FunctionId) -> Vec<Job> {
        let module = self.function_module(function);
        if module.is_global() {
            return self.code.ids().into_iter().map(Job::ScopeCode).collect();
        }
        self.ensure_runtime_module(module);
        vec![Job::DefineModule(module)]
    }

    pub(crate) fn wait_for_function_definition(&mut self, function: FunctionId) -> JobEffects {
        JobEffects::wait_on(FactKey::FunctionDefined(function), vec![Job::DefineFunction(function)])
    }

    /// Demands and waits on the module whose definition notes `module`'s
    /// `@type`s — the type-side mirror of `wait_for_function_definition`. Used
    /// only for non-global modules; a top-level type is noted by its code scope.
    pub(crate) fn wait_for_type_decl(&mut self, module: ModuleId) -> JobEffects {
        self.ensure_runtime_module(module);
        JobEffects::wait_on(FactKey::ModuleDefined(module), vec![Job::DefineModule(module)])
    }

    pub fn fact_revision(&self, key: FactKey) -> Option<u64> {
        self.work_graph.facts().revision(&key)
    }

    #[cfg(test)]
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

    #[cfg(test)]
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

    #[cfg(test)]
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

    pub(crate) fn fact_would_change(&self, key: FactKey, revision: u64) -> bool {
        self.fact_revision(key) != Some(revision)
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
                NamespaceSymbol::Module(_) | NamespaceSymbol::Type(_) => None,
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
                NamespaceSymbol::Module(_) | NamespaceSymbol::Type(_) => {
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
        match &self.code.get(id).state {
            super::code::CodeState::Indexed { source, .. } => Some(source.clone()),
            super::code::CodeState::Pending => None,
        }
    }

    pub fn code_surface(&self, id: CodeId) -> Option<&super::quoted_surface::ScopeSurface> {
        match &self.code.get(id).state {
            super::code::CodeState::Indexed { source } => Some(&source.surface),
            super::code::CodeState::Pending => None,
        }
    }

    pub fn module_scope(&self, module: ModuleId) -> Option<(super::identity::ModuleSource, ScopeSnapshot)> {
        match &self.modules.get(module).state {
            ModuleState::Scoped { source, base } => Some((source.clone(), ScopeSnapshot::module(module, *base))),
            ModuleState::Defined { source, surface } => {
                Some((source.clone(), ScopeSnapshot::module(module, surface.base)))
            }
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
            ModuleSourceKind::Protocol(protocol)
                if protocol.forms.iter().any(|form| match form {
                    super::quoted_surface::ScopeForm::Function(callback) => {
                        callback.name == function_ref.name && callback.arity == function_ref.arity
                    }
                    _ => false,
                }) =>
            {
                Some(ProtocolCallback {
                    protocol: function_ref.module,
                })
            }
            ModuleSourceKind::Body(_) | ModuleSourceKind::Protocol(_) => None,
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
            FactKey::FunctionSource(function) => self.unresolved_function_issue(frontier, *function),
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

/// A consumer's references are a set: the same type named twice (e.g. by both a
/// spec and a parameter annotation) is one dependency. Order is preserved.
fn dedup_type_names(refs: &mut Vec<TypeName>) {
    let mut seen = HashSet::new();
    refs.retain(|name| seen.insert(name.clone()));
}

#[cfg(test)]
fn module_name_segments(name: &str) -> Vec<String> {
    name.split('.')
        .filter(|segment| !segment.is_empty())
        .map(str::to_string)
        .collect()
}

fn protocol_domain_type_name(protocol: ModuleId, arity: usize) -> TypeName {
    TypeName {
        module: protocol,
        name: "t".to_string(),
        arity,
    }
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
