//! Compiler2's owned world state.
//!
//! Compiler-owned identities are total here. A `CodeId`, `ModuleId`,
//! `FunctionId`, or `RootId` that came from Compiler2 must resolve; a bad id is
//! a bug and should panic at the lookup boundary. `Option` is reserved for
//! legitimate state absence like "this known function is still a placeholder"
//! or "this known code has not been indexed yet".

use std::rc::Rc;

use crate::ast::FnDef;
use crate::ast::Item;
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardDispatch};
use crate::telemetry::{Telemetry, opaque};
use crate::type_expr::{ModuleTypeEnv, build_module_type_env_for_with_base, builtin_type_env};
use crate::types;
use crate::{measurements, metadata};

use super::CodeId;
use super::body::{LoweredBody, LoweredBodyMap};
use super::code::CodeMap;
use super::deps::ExactPattern;
use super::dispatch::{EntryDispatchMap, GuardDispatchMap};
use super::drive::{FactKey, Job, JobEffects, WorkGraph};
use super::identity::{
    ExecutableNeed, FunctionDef, FunctionId, FunctionMap, ModuleExport, ModuleId, ModuleMap, ModuleState, RootEntry,
    RootId, RootMap,
};
use super::namespace::{Namespace, NamespaceStore, NamespaceSymbol};

pub struct World<'a> {
    tel: &'a dyn Telemetry,
    code: CodeMap,
    modules: ModuleMap,
    functions: FunctionMap,
    bodies: LoweredBodyMap,
    guard_dispatches: GuardDispatchMap,
    entry_dispatches: EntryDispatchMap,
    roots: RootMap,
    namespaces: NamespaceStore,
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
            .field("work_graph", &self.work_graph)
            .finish()
    }
}

impl<'a> World<'a> {
    pub fn new(tel: &'a dyn Telemetry) -> Self {
        Self {
            tel,
            code: CodeMap::new(),
            modules: ModuleMap::new(),
            functions: FunctionMap::new(),
            bodies: LoweredBodyMap::new(),
            guard_dispatches: GuardDispatchMap::new(),
            entry_dispatches: EntryDispatchMap::new(),
            roots: RootMap::new(),
            namespaces: NamespaceStore::new(),
            work_graph: WorkGraph::new(),
        }
    }

    pub fn tel(&self) -> &'a dyn Telemetry {
        self.tel
    }

    pub fn submit_code(&mut self, name: Option<String>, text: String) -> CodeId {
        let submitted_name = name.clone();
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
            &metadata! {
                name: submitted_name.as_deref().unwrap_or("<anonymous>"),
            },
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
        self.tel.execute(
            &["fz", "compiler2", "root", "submitted"],
            &measurements! {
                root_id: root_id.as_u32() as u64,
                function_id: function.as_u32() as u64,
                arity: arity as u64,
                pending_codes: self.code.len() as u64,
            },
            &metadata! {
                module_name: module_name.as_deref().unwrap_or("<top-level>"),
                name: name.as_str(),
                need: need.as_str(),
            },
        );
        root_id
    }

    pub(crate) fn complete_job(&mut self, job: Job, effects: JobEffects) {
        let reads = effects.reads.into_iter().collect();
        let waits = effects.waits.into_iter().map(ExactPattern).collect();
        let _ = self
            .work_graph
            .complete(job, reads, waits, effects.outputs, effects.follow_up);
    }

    pub fn demand(&mut self, job: Job) -> bool {
        self.work_graph.enqueue(job)
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

    pub fn reference_module(&mut self, name: impl Into<String>) -> ModuleId {
        self.modules.reference_named(name)
    }

    pub fn reference_child_module(&mut self, parent: ModuleId, local_name: &str) -> ModuleId {
        let name = self.qualified_module_name(parent, local_name);
        self.modules.reference_named(name)
    }

    pub fn define_module(&mut self, id: ModuleId, namespace: Namespace, exports: Vec<ModuleExport>) -> u64 {
        let (code, name) = self.module_definition_metadata(id);
        let revision = self.modules.define(id, code, namespace, exports);
        let source_name = self.code.name(code).unwrap_or("<anonymous>");
        self.tel.execute(
            &["fz", "compiler2", "module", "defined"],
            &measurements! {
                code_id: code.as_u32() as u64,
                module_id: id.as_u32() as u64,
                revision: revision,
            },
            &metadata! {
                source_name: source_name,
                module_name: name.as_str(),
            },
        );
        revision
    }

    pub fn index_module(
        &mut self,
        id: ModuleId,
        code: CodeId,
        parent: ModuleId,
        local_name: String,
        attrs: Vec<crate::ast::Attribute>,
        items: Vec<Rc<Item>>,
    ) -> u64 {
        self.modules.index(id, code, parent, local_name, attrs, items)
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
        local_name: String,
        code: CodeId,
        namespace: Namespace,
        ast: FnDef,
    ) -> (FunctionId, u64) {
        let arity = ast.arity();
        let id = self.functions.reference(module, local_name.clone(), arity);
        let module_name = (!module.is_global()).then(|| self.modules.name(module)).flatten();
        let fq_name = match module_name {
            Some(module_name) => format!("{module_name}.{local_name}"),
            None => local_name.clone(),
        };
        let source_name = self.code.name(code).unwrap_or("<anonymous>");
        let kind = if ast.is_macro { "macro" } else { "function" };
        let visibility = if ast.is_private { "private" } else { "public" };
        let clauses = ast.clauses.len() as u64;
        let revision = self.functions.define(id, FunctionDef { code, namespace, ast });
        self.tel.execute(
            &["fz", "compiler2", "function", "defined"],
            &measurements! {
                code_id: code.as_u32() as u64,
                function_id: id.as_u32() as u64,
                revision: revision,
                arity: arity as u64,
                clauses: clauses,
            },
            &metadata! {
                source_name: source_name,
                module_name: module_name.unwrap_or("<top-level>"),
                name: local_name.as_str(),
                fq_name: fq_name.as_str(),
                kind: kind,
                visibility: visibility,
            },
        );
        (id, revision)
    }

    pub(crate) fn define_generated_function(
        &mut self,
        owner: FunctionId,
        namespace: Namespace,
        ast: FnDef,
    ) -> (FunctionId, u64) {
        let owner_module = self.functions.reference_for(owner).module;
        let owner_code = self.function_definition(owner).code;
        let id = self
            .functions
            .reference_generated(owner, owner_module, ast.span, ast.arity());
        let revision = self.functions.define(
            id,
            super::identity::FunctionDef {
                code: owner_code,
                namespace,
                ast: ast.clone(),
            },
        );
        let module_name = if owner_module.is_global() {
            "<top-level>".to_string()
        } else {
            self.modules
                .name(owner_module)
                .expect("generated function modules should have a reverse lookup")
                .to_string()
        };
        let source_name = self.code.name(owner_code).unwrap_or("<anonymous>");
        self.tel.execute(
            &["fz", "compiler2", "function", "defined"],
            &measurements! {
                code_id: owner_code.as_u32() as u64,
                function_id: id.as_u32() as u64,
                revision: revision,
                arity: ast.arity() as u64,
                clauses: ast.clauses.len() as u64,
                owner_function_id: owner.as_u32() as u64,
            },
            &metadata! {
                source_name: source_name,
                module_name: module_name.as_str(),
                name: ast.name.as_str(),
                fq_name: ast.name.as_str(),
                kind: "generated",
                visibility: "private",
            },
        );
        (id, revision)
    }

    pub(crate) fn define_lowered_body(&mut self, function: FunctionId, body: LoweredBody) -> u64 {
        self.bodies.define(function, body)
    }

    pub(crate) fn define_guard_dispatch(&mut self, function: FunctionId, dispatch: PatternGuardDispatch) -> u64 {
        let def = self.function_definition(function);
        let function_ref = self.functions.reference_for(function);
        let module_name = if function_ref.module.is_global() {
            "<top-level>".to_string()
        } else {
            self.modules
                .name(function_ref.module)
                .expect("named guard dispatch modules should have a reverse lookup")
                .to_string()
        };
        let fq_name = if module_name == "<top-level>" {
            function_ref.name.clone()
        } else {
            format!("{}.{}", module_name, function_ref.name)
        };
        let revision = self.guard_dispatches.define(function, dispatch.clone());
        self.tel.execute(
            &["fz", "compiler2", "guard_dispatch", "defined"],
            &measurements! {
                code_id: def.code.as_u32() as u64,
                function_id: function.as_u32() as u64,
                revision: revision,
                arity: def.ast.arity() as u64,
                bodies: dispatch.bodies.len() as u64,
                guards: dispatch.plan.guards.len() as u64,
                pinned: dispatch.plan.pinned.len() as u64,
            },
            &metadata! {
                source_name: self.code.name(def.code).unwrap_or("<anonymous>"),
                module_name: module_name.as_str(),
                name: function_ref.name.as_str(),
                fq_name: fq_name.as_str(),
                dispatch: opaque(&dispatch),
            },
        );
        revision
    }

    pub(crate) fn define_entry_dispatch(&mut self, function: FunctionId, plan: PatternDispatchPlan) -> u64 {
        let def = self.function_definition(function);
        let function_ref = self.functions.reference_for(function);
        let module_name = if function_ref.module.is_global() {
            "<top-level>".to_string()
        } else {
            self.modules
                .name(function_ref.module)
                .expect("named entry dispatch modules should have a reverse lookup")
                .to_string()
        };
        let fq_name = if module_name == "<top-level>" {
            function_ref.name.clone()
        } else {
            format!("{}.{}", module_name, function_ref.name)
        };
        let revision = self.entry_dispatches.define(function, plan.clone());
        self.tel.execute(
            &["fz", "compiler2", "entry_dispatch", "defined"],
            &measurements! {
                code_id: def.code.as_u32() as u64,
                function_id: function.as_u32() as u64,
                revision: revision,
                arity: def.ast.arity() as u64,
                outcomes: plan.outcomes.len() as u64,
                guards: plan.guards.len() as u64,
                pinned: plan.pinned.len() as u64,
            },
            &metadata! {
                source_name: self.code.name(def.code).unwrap_or("<anonymous>"),
                module_name: module_name.as_str(),
                name: function_ref.name.as_str(),
                fq_name: fq_name.as_str(),
                plan: opaque(&plan),
            },
        );
        revision
    }

    pub fn prelude_head(&self) -> Namespace {
        self.namespaces.prelude_head()
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
        self.work_graph.facts().get(&FactKey::ModuleDefined(module))
    }

    pub fn function_defined_revision(&self, function: FunctionId) -> Option<u64> {
        if !matches!(
            self.functions.get(function).state,
            super::identity::FunctionState::Defined { .. }
        ) {
            return None;
        }
        self.work_graph.facts().get(&FactKey::FunctionDefined(function))
    }

    pub(crate) fn function_definition(&self, function: FunctionId) -> super::identity::FunctionDef {
        match &self.functions.get(function).state {
            super::identity::FunctionState::Defined { def } => def.clone(),
            super::identity::FunctionState::Placeholder => {
                panic!("function definitions should only be read from defined functions")
            }
        }
    }

    pub(crate) fn function_module(&self, function: FunctionId) -> ModuleId {
        self.functions.reference_for(function).module
    }

    pub fn fact_revision(&self, key: FactKey) -> Option<u64> {
        self.work_graph.facts().get(&key)
    }

    pub(crate) fn lookup_callable_namespace(
        &self,
        head: Namespace,
        name: &str,
        arity: usize,
    ) -> Option<NamespaceSymbol> {
        self.namespaces
            .lookup_matching(head, name, |symbol| match symbol {
                NamespaceSymbol::Function(function) | NamespaceSymbol::Macro(function) => {
                    self.functions.reference_for(*function).arity == arity
                }
                NamespaceSymbol::Module(_) => false,
            })
            .cloned()
    }

    pub(crate) fn guard_dispatch(&self, function: FunctionId) -> PatternGuardDispatch {
        self.guard_dispatches
            .get(function)
            .cloned()
            .expect("guard dispatch should only be read after its fact is defined")
    }

    pub(crate) fn function_type_env(
        &self,
        function: FunctionId,
    ) -> Result<ModuleTypeEnv, crate::type_expr::TypeExprError> {
        let module = self.functions.reference_for(function).module;
        let mut types = types::new();
        let builtin_env = builtin_type_env(&mut types);
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
        build_module_type_env_for_with_base(&mut types, &attrs, &module_name, &builtin_env).map(|(env, _, _)| env)
    }

    pub fn code_items(&self, id: CodeId) -> Option<&[Rc<Item>]> {
        match &self.code.get(id).state {
            super::code::CodeState::Indexed { items } => Some(items.as_slice()),
            super::code::CodeState::Pending => None,
        }
    }

    pub fn module_scope(&self, module: ModuleId) -> Option<(CodeId, Vec<Rc<Item>>, Namespace)> {
        match &self.modules.get(module).state {
            ModuleState::Scoped { source, base } => Some((source.code, source.items.clone(), *base)),
            ModuleState::Defined { source, surface } => Some((source.code, source.items.clone(), surface.base)),
            _ => None,
        }
    }

    pub fn module_indexed_parent(&self, module: ModuleId) -> Option<(CodeId, ModuleId)> {
        match &self.modules.get(module).state {
            ModuleState::Indexed(source) => Some((source.code, source.parent)),
            _ => None,
        }
    }

    fn module_definition_metadata(&self, module: ModuleId) -> (CodeId, String) {
        match &self.modules.get(module).state {
            ModuleState::Scoped { source, .. } | ModuleState::Defined { source, .. } => (
                source.code,
                self.qualified_module_name(source.parent, &source.local_name),
            ),
            ModuleState::Placeholder | ModuleState::Indexed(_) => {
                panic!("modules should be scoped before definition")
            }
        }
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
}
