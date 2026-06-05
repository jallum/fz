#![allow(dead_code)]
// fz-hua.2 makes Compiler the owner of source-backed module state, but the
// later world-model phases are still being pulled into use over the next
// tickets. Keep the allowance local to this module until those phases are live.

use crate::ast::{Attribute, FnDef, Item, ModuleDef, Program, ProtocolImplDef, SpecDecl};
use crate::diag::{Diagnostic, SourceMap, Span};
use crate::frontend::resolve::{InterfaceTable, ModuleContractRequest, ResolveDemandResult, resolve_program_once};
use crate::frontend::{
    FrontendErr, FrontendOk, FrontendResult, apply_planned_direct_call_targets, check_frontend_from_entry_fns, macros,
    protocols::{ImplTarget, ProtocolDecl, ProtocolImplFact, ProtocolImplKey, extend_protocol_facts_from_interfaces},
    resolve,
};
use crate::fz_ir::{BlockId, ExternDecl, ExternId, ExternTy, ExternalCallEdge, FnId, FnIr, ProtocolCallTarget, Var};
use crate::ir_lower::{
    ExternTable, FnKey, LowerError, LoweringDemandResult, begin_compiler_lowering_session, collect_lowerable_fn_keys,
    select_initial_root_fn_keys,
};
use crate::ir_planner::{ModulePlan, plan_module, plan_module_from_entry_fns, rewrite_closed_union_protocol_dispatch};
pub(crate) use crate::modules::identity::ModuleId;
use crate::modules::identity::{ExportKey, Mfa, ModuleName};
use crate::modules::interface::{InterfaceSpec, ModuleInterface, collect_from_program};
use crate::modules::runtime_library::{self, RUNTIME_MODULE_SOURCES, RUNTIME_PRELUDE_FZ};
use crate::parser::Parser;
use crate::parser::lexer::Lexer;
use crate::telemetry::NullTelemetry;
use crate::telemetry::value::opaque;
use crate::telemetry::{Telemetry, TelemetryExt as _};
use crate::types;
use crate::types::{ClosureTypes, DefaultTypes, LiteralTypes, RenderTypes, Ty, Types};
use crate::{measurements, metadata};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::error::Error;
use std::fmt;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct FileId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct FnGroupId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct NamespaceId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ModuleKey {
    RootPath(PathBuf),
    Named(ModuleName),
}

impl ModuleKey {
    fn render(&self) -> String {
        match self {
            ModuleKey::RootPath(path) => path.display().to_string(),
            ModuleKey::Named(name) => name.to_string(),
        }
    }

    fn kind(&self) -> &'static str {
        match self {
            ModuleKey::RootPath(_) => "root_path",
            ModuleKey::Named(_) => "named",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ModuleOrigin {
    RootSource,
    Filesystem,
    Supplemental,
    EmbeddedRuntime,
    PrimitivePrelude,
}

impl ModuleOrigin {
    pub(crate) fn kind(self) -> &'static str {
        match self {
            ModuleOrigin::RootSource => "root_source",
            ModuleOrigin::Filesystem => "filesystem",
            ModuleOrigin::Supplemental => "supplemental",
            ModuleOrigin::EmbeddedRuntime => "embedded_runtime",
            ModuleOrigin::PrimitivePrelude => "primitive_prelude",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum FileOrigin {
    Filesystem(PathBuf),
    Synthetic(String),
    Supplemental(String),
    EmbeddedRuntime(String),
    PrimitivePrelude(String),
}

impl FileOrigin {
    fn kind(&self) -> &'static str {
        match self {
            FileOrigin::Filesystem(_) => "filesystem",
            FileOrigin::Synthetic(_) => "synthetic",
            FileOrigin::Supplemental(_) => "supplemental",
            FileOrigin::EmbeddedRuntime(_) => "embedded_runtime",
            FileOrigin::PrimitivePrelude(_) => "primitive_prelude",
        }
    }

    fn render(&self) -> String {
        match self {
            FileOrigin::Filesystem(path) => path.display().to_string(),
            FileOrigin::Synthetic(name)
            | FileOrigin::Supplemental(name)
            | FileOrigin::EmbeddedRuntime(name)
            | FileOrigin::PrimitivePrelude(name) => name.clone(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ModuleReadinessFact {
    SourceReady,
    Parsed,
    NamespaceReady,
    BodySurfaceReady,
    InterfaceTableReady,
    MacroSurfaceReady,
    RuntimeLowered,
    RuntimePlanned,
}

impl ModuleReadinessFact {
    fn as_str(self) -> &'static str {
        match self {
            ModuleReadinessFact::SourceReady => "source_ready",
            ModuleReadinessFact::Parsed => "parsed",
            ModuleReadinessFact::NamespaceReady => "namespace_ready",
            ModuleReadinessFact::BodySurfaceReady => "body_surface_ready",
            ModuleReadinessFact::InterfaceTableReady => "interface_table_ready",
            ModuleReadinessFact::MacroSurfaceReady => "macro_surface_ready",
            ModuleReadinessFact::RuntimeLowered => "runtime_lowered",
            ModuleReadinessFact::RuntimePlanned => "runtime_planned",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) struct ModuleReadiness {
    pub(crate) source_ready: bool,
    pub(crate) parsed: bool,
    pub(crate) namespace_ready: bool,
    pub(crate) body_surface_ready: bool,
    pub(crate) interface_table_ready: bool,
    pub(crate) macro_surface_ready: bool,
    pub(crate) runtime_lowered: bool,
    pub(crate) runtime_planned: bool,
}

impl ModuleReadiness {
    pub(crate) fn has(self, fact: ModuleReadinessFact) -> bool {
        match fact {
            ModuleReadinessFact::SourceReady => self.source_ready,
            ModuleReadinessFact::Parsed => self.parsed,
            ModuleReadinessFact::NamespaceReady => self.namespace_ready,
            ModuleReadinessFact::BodySurfaceReady => self.body_surface_ready,
            ModuleReadinessFact::InterfaceTableReady => self.interface_table_ready,
            ModuleReadinessFact::MacroSurfaceReady => self.macro_surface_ready,
            ModuleReadinessFact::RuntimeLowered => self.runtime_lowered,
            ModuleReadinessFact::RuntimePlanned => self.runtime_planned,
        }
    }

    fn record(&mut self, fact: ModuleReadinessFact) {
        match fact {
            ModuleReadinessFact::SourceReady => self.source_ready = true,
            ModuleReadinessFact::Parsed => self.parsed = true,
            ModuleReadinessFact::NamespaceReady => self.namespace_ready = true,
            ModuleReadinessFact::BodySurfaceReady => self.body_surface_ready = true,
            ModuleReadinessFact::InterfaceTableReady => self.interface_table_ready = true,
            ModuleReadinessFact::MacroSurfaceReady => self.macro_surface_ready = true,
            ModuleReadinessFact::RuntimeLowered => self.runtime_lowered = true,
            ModuleReadinessFact::RuntimePlanned => self.runtime_planned = true,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReachabilityKind {
    Interface,
    Macro,
    Runtime,
}

impl ReachabilityKind {
    fn as_str(self) -> &'static str {
        match self {
            ReachabilityKind::Interface => "interface",
            ReachabilityKind::Macro => "macro",
            ReachabilityKind::Runtime => "runtime",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) struct Reachability {
    pub(crate) interface: bool,
    pub(crate) macros: bool,
    pub(crate) runtime: bool,
}

impl Reachability {
    fn is_marked(self, kind: ReachabilityKind) -> bool {
        match kind {
            ReachabilityKind::Interface => self.interface,
            ReachabilityKind::Macro => self.macros,
            ReachabilityKind::Runtime => self.runtime,
        }
    }

    fn mark(&mut self, kind: ReachabilityKind) {
        match kind {
            ReachabilityKind::Interface => self.interface = true,
            ReachabilityKind::Macro => self.macros = true,
            ReachabilityKind::Runtime => self.runtime = true,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ParseKind {
    Program,
    Prelude,
}

impl ParseKind {
    fn as_str(self) -> &'static str {
        match self {
            ParseKind::Program => "program",
            ParseKind::Prelude => "prelude",
        }
    }
}

#[derive(Debug, Clone)]
struct SourceDescriptor {
    source_name: String,
    text: Arc<str>,
    parse_kind: ParseKind,
}

#[derive(Clone)]
pub(crate) struct ParsedProgram {
    pub(crate) sm: SourceMap,
    pub(crate) program: Program,
}

#[derive(Clone)]
pub(crate) struct ParsedPrelude {
    pub(crate) sm: SourceMap,
    pub(crate) items: Vec<Rc<Item>>,
    pub(crate) attrs: Vec<Attribute>,
}

#[derive(Clone)]
pub(crate) enum ParsedSource {
    Program(ParsedProgram),
    Prelude(ParsedPrelude),
}

impl ParsedSource {
    fn parse_kind(&self) -> ParseKind {
        match self {
            ParsedSource::Program(_) => ParseKind::Program,
            ParsedSource::Prelude(_) => ParseKind::Prelude,
        }
    }

    fn item_count(&self) -> usize {
        match self {
            ParsedSource::Program(parsed) => parsed.program.items.len(),
            ParsedSource::Prelude(parsed) => parsed.items.len() + parsed.attrs.len(),
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct PreparedPrelude {
    pub(crate) program: Program,
    pub(crate) imports: HashMap<(String, usize), String>,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct SourceMacroExports {
    pub(crate) root: HashSet<(String, usize)>,
    pub(crate) modules: HashMap<ModuleName, HashSet<(String, usize)>>,
}

#[derive(Debug, Clone)]
pub(crate) struct ModuleMacroSurface {
    pub(crate) exports: HashSet<(String, usize)>,
    pub(crate) program: Program,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct AnonymousFunctionId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum FunctionKey {
    Named(Mfa),
    Anonymous(AnonymousFunctionId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum FunctionKind {
    Source,
    Continuation,
    Lambda,
    ExternWrapper,
    ExternalStub,
    ImportedFnValueWrapper,
    ProtocolStub,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum FunctionContractState {
    Referenced,
    Declared,
    SourceReady,
    InterfaceReady,
    SourceAndInterfaceReady,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ExternFunctionDecl {
    pub(crate) symbol: String,
    pub(crate) params: Vec<ExternTy>,
    pub(crate) variadic: bool,
    pub(crate) ret: ExternTy,
    pub(crate) ret_descr: Ty,
}

#[derive(Debug, Clone)]
pub(crate) struct FunctionRecord {
    pub(crate) id: FnId,
    pub(crate) owner_module_id: ModuleId,
    pub(crate) key: FunctionKey,
    pub(crate) kind: FunctionKind,
    pub(crate) debug_name: String,
    pub(crate) contract_state: FunctionContractState,
    pub(crate) declared_extern: Option<ExternFunctionDecl>,
    pub(crate) declared_source_specs: Vec<SpecDecl>,
    pub(crate) declared_interface_specs: Vec<InterfaceSpec>,
}

#[derive(Debug, Clone)]
pub(crate) enum FnGroupInput {
    SourceFn(Rc<FnDef>),
}

pub(crate) type SourceFnKey = Mfa;

#[derive(Debug, Clone)]
pub(crate) struct FnGroupDescriptor {
    pub(crate) id: FnGroupId,
    pub(crate) source: SourceFnKey,
    pub(crate) owner_module: String,
    pub(crate) qualified_name: String,
    pub(crate) is_private: bool,
    pub(crate) input: FnGroupInput,
}

impl FnGroupDescriptor {
    pub(crate) fn fn_def(&self) -> &FnDef {
        match &self.input {
            FnGroupInput::SourceFn(def) => def,
        }
    }

    pub(crate) fn qualified_name(&self) -> &str {
        &self.qualified_name
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct ModuleBodySurface {
    pub(crate) owner_module_id: ModuleId,
    pub(crate) owner_module: String,
    pub(crate) groups: Vec<FnGroupDescriptor>,
    pub(crate) group_by_source: HashMap<SourceFnKey, FnGroupId>,
}

impl ModuleBodySurface {
    fn register_source_group(
        &mut self,
        owner_module_id: ModuleId,
        owner_module: &str,
        qualified_name: String,
        def: Rc<FnDef>,
    ) {
        let group_id = FnGroupId(self.groups.len() as u32);
        let arity = def.clauses.first().map(|clause| clause.params.len()).unwrap_or(0);
        let source = SourceFnKey::new(owner_module_id, def.name.clone(), arity);
        self.groups.push(FnGroupDescriptor {
            id: group_id,
            source: source.clone(),
            owner_module: owner_module.to_string(),
            qualified_name,
            is_private: def.is_private,
            input: FnGroupInput::SourceFn(def),
        });
        self.group_by_source.insert(source, group_id);
    }
}

#[derive(Debug, Clone)]
pub(crate) struct LoweredFnGroup {
    pub(crate) id: FnGroupId,
    pub(crate) source: SourceFnKey,
    pub(crate) function_ids: Vec<FnId>,
    pub(crate) fns: Vec<FnIr>,
    pub(crate) atom_names: Vec<String>,
    pub(crate) extern_decls: Vec<ExternDecl>,
    pub(crate) external_call_edges: Vec<ExternalCallEdge>,
    pub(crate) protocol_call_targets: HashMap<FnId, ProtocolCallTarget>,
    pub(crate) fn_spans: HashMap<FnId, Span>,
    pub(crate) stmt_spans: HashMap<(FnId, BlockId), Vec<Span>>,
    pub(crate) term_spans: HashMap<(FnId, BlockId), Span>,
    pub(crate) var_meta: HashMap<(FnId, Var), (Span, String)>,
    pub(crate) continuation_provenance: HashMap<FnId, crate::fz_ir::ContinuationProvenance>,
    pub(crate) extern_wrappers: HashMap<ExternId, FnId>,
    pub(crate) external_stubs: HashMap<ExportKey, FnId>,
    pub(crate) imported_fn_value_wrappers: HashMap<ExportKey, FnId>,
    pub(crate) protocol_stubs: HashMap<(String, usize), FnId>,
}

#[derive(Debug, Clone)]
pub(crate) struct RuntimeReachabilitySeed {
    pub(crate) module_id: ModuleId,
    pub(crate) entry: Option<Mfa>,
    pub(crate) reason: &'static str,
    pub(crate) from_module: Option<ModuleName>,
}

impl RuntimeReachabilitySeed {
    pub(crate) fn new(module_id: ModuleId, reason: &'static str, from_module: Option<ModuleName>) -> Self {
        Self {
            module_id,
            entry: None,
            reason,
            from_module,
        }
    }

    pub(crate) fn with_entry(mut self, name: impl Into<String>, arity: usize) -> Self {
        self.entry = Some(Mfa::new(self.module_id, name, arity));
        self
    }

    pub(crate) fn with_mfa(mut self, mfa: Mfa) -> Self {
        self.entry = Some(mfa);
        self
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ModuleContractOrigin {
    CompilerOwned(ModuleOrigin),
    Supplemental,
}

impl ModuleContractOrigin {
    pub(crate) fn kind(&self) -> &'static str {
        match self {
            Self::CompilerOwned(origin) => origin.kind(),
            Self::Supplemental => "supplemental",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ModuleContractRecord {
    pub(crate) interface: ModuleInterface,
    pub(crate) origin: ModuleContractOrigin,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum VisibleCallableAliasOrigin {
    SourceDeclaration,
    Imported { from_module: ModuleName },
    PreludeImport { from_module: ModuleName },
}

impl VisibleCallableAliasOrigin {
    fn kind(&self) -> &'static str {
        match self {
            Self::SourceDeclaration => "source_declaration",
            Self::Imported { .. } => "imported",
            Self::PreludeImport { .. } => "prelude_import",
        }
    }

    fn from_module(&self) -> Option<&ModuleName> {
        match self {
            Self::SourceDeclaration => None,
            Self::Imported { from_module } | Self::PreludeImport { from_module } => Some(from_module),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct VisibleCallableAlias {
    pub(crate) name: String,
    pub(crate) arity: usize,
    pub(crate) target: Mfa,
    pub(crate) origin: VisibleCallableAliasOrigin,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum VisibleModuleBindingOrigin {
    ChildModule,
    Alias,
    PreludeAlias,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct VisibleModuleBinding {
    pub(crate) name: String,
    pub(crate) target_module_id: ModuleId,
    pub(crate) origin: VisibleModuleBindingOrigin,
}

#[derive(Debug, Clone)]
pub(crate) struct NamespaceRecord {
    pub(crate) id: NamespaceId,
    pub(crate) owner_module_id: ModuleId,
    pub(crate) parent: Option<NamespaceId>,
    pub(crate) callable_bindings: HashMap<(String, usize), VisibleCallableAlias>,
    pub(crate) module_bindings: HashMap<String, VisibleModuleBinding>,
}

#[derive(Debug, Clone)]
pub(crate) struct ModuleRecord {
    pub(crate) id: ModuleId,
    pub(crate) key: Option<ModuleKey>,
    pub(crate) declaration: Option<ModuleDeclaration>,
    pub(crate) namespace_id: NamespaceId,
    pub(crate) readiness: ModuleReadiness,
    pub(crate) reachability: Reachability,
    pub(crate) body_surface: Option<ModuleBodySurface>,
    pub(crate) lowered_groups: HashMap<SourceFnKey, LoweredFnGroup>,
    pub(crate) runtime_entry_fns: HashSet<Mfa>,
    pub(crate) runtime_materialized_entry_fns: HashSet<Mfa>,
    pub(crate) runtime_lowered_functions: Option<usize>,
    pub(crate) runtime_planned_specs: Option<usize>,
    pub(crate) interfaces: Option<BTreeMap<ModuleName, ModuleInterface>>,
    pub(crate) contract: Option<ModuleContractRecord>,
    pub(crate) macro_exports: Option<HashSet<(String, usize)>>,
    pub(crate) macro_surface: Option<ModuleMacroSurface>,
    pub(crate) prepared_prelude: Option<PreparedPrelude>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ModuleDeclaration {
    pub(crate) origin: ModuleOrigin,
    pub(crate) file_id: FileId,
}

impl ModuleRecord {
    fn key_render(&self) -> String {
        self.key
            .as_ref()
            .map(ModuleKey::render)
            .unwrap_or_else(|| "<anonymous>".to_string())
    }

    fn key_kind(&self) -> &'static str {
        self.key.as_ref().map(ModuleKey::kind).unwrap_or("anonymous")
    }

    pub(crate) fn origin(&self) -> Option<ModuleOrigin> {
        self.declaration.map(|declaration| declaration.origin)
    }

    pub(crate) fn file_id(&self) -> Option<FileId> {
        self.declaration.map(|declaration| declaration.file_id)
    }
}

#[derive(Clone)]
pub(crate) struct FileRecord {
    pub(crate) id: FileId,
    pub(crate) origin: FileOrigin,
    source: Option<Arc<str>>,
    descriptor: SourceDescriptor,
    parsed: Option<ParsedSource>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CompilerInvariantError {
    message: String,
}

impl CompilerInvariantError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for CompilerInvariantError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl Error for CompilerInvariantError {}

pub(crate) struct CompilerWorld {
    modules: Vec<ModuleRecord>,
    namespaces: Vec<NamespaceRecord>,
    files: Vec<FileRecord>,
    functions: Vec<FunctionRecord>,
    extern_decls: Vec<ExternDecl>,
    module_index: BTreeMap<ModuleKey, ModuleId>,
    file_index: BTreeMap<FileOrigin, FileId>,
    named_function_ids: HashMap<Mfa, FnId>,
    named_function_keys: HashMap<FnId, Mfa>,
    extern_name_ids: HashMap<String, ExternId>,
    protocol_decls: BTreeMap<ModuleName, ProtocolDecl>,
    protocol_impls: BTreeMap<ProtocolImplKey, ProtocolImplFact>,
    protocol_callback_owners: BTreeMap<ExportKey, ModuleName>,
    protocol_provider_modules: BTreeMap<ModuleName, BTreeSet<ModuleName>>,
    next_anonymous_function_id: u32,
}

pub(crate) struct Compiler {
    types: DefaultTypes,
    world: CompilerWorld,
}

impl CompilerWorld {
    pub(crate) fn new() -> Self {
        Self {
            modules: Vec::new(),
            namespaces: Vec::new(),
            files: Vec::new(),
            functions: Vec::new(),
            extern_decls: Vec::new(),
            module_index: BTreeMap::new(),
            file_index: BTreeMap::new(),
            named_function_ids: HashMap::new(),
            named_function_keys: HashMap::new(),
            extern_name_ids: HashMap::new(),
            protocol_decls: BTreeMap::new(),
            protocol_impls: BTreeMap::new(),
            protocol_callback_owners: BTreeMap::new(),
            protocol_provider_modules: BTreeMap::new(),
            next_anonymous_function_id: 0,
        }
    }

    pub(crate) fn module_count(&self) -> usize {
        self.modules.len()
    }

    pub(crate) fn file_count(&self) -> usize {
        self.files.len()
    }

    pub(crate) fn namespace(&self, namespace_id: NamespaceId) -> &NamespaceRecord {
        &self.namespaces[namespace_id.0 as usize]
    }

    fn namespace_mut(&mut self, namespace_id: NamespaceId) -> &mut NamespaceRecord {
        &mut self.namespaces[namespace_id.0 as usize]
    }

    pub(crate) fn function_count(&self) -> usize {
        self.functions.len()
    }

    pub(crate) fn extern_count(&self) -> usize {
        self.extern_decls.len()
    }

    pub(crate) fn module(&self, id: ModuleId) -> &ModuleRecord {
        &self.modules[id.0 as usize]
    }

    pub(crate) fn module_origin(&self, id: ModuleId) -> Option<ModuleOrigin> {
        self.module(id).origin()
    }

    pub(crate) fn declared_module_origin(&self, id: ModuleId) -> ModuleOrigin {
        self.module_origin(id)
            .unwrap_or_else(|| panic!("module `{}` has no declaration", self.module_key_render(id)))
    }

    pub(crate) fn module_file_id(&self, id: ModuleId) -> Option<FileId> {
        self.module(id).file_id()
    }

    pub(crate) fn declared_module_file_id(&self, id: ModuleId) -> FileId {
        self.module_file_id(id)
            .unwrap_or_else(|| panic!("module `{}` has no declaration", self.module_key_render(id)))
    }

    pub(crate) fn file(&self, id: FileId) -> &FileRecord {
        &self.files[id.0 as usize]
    }

    pub(crate) fn function(&self, id: FnId) -> &FunctionRecord {
        &self.functions[id.0 as usize]
    }

    pub(crate) fn module_key_render(&self, id: ModuleId) -> String {
        self.modules[id.0 as usize].key_render()
    }

    pub(crate) fn module_display_name(&self, id: ModuleId) -> String {
        match &self.module(id).key {
            None | Some(ModuleKey::RootPath(_)) => String::new(),
            Some(ModuleKey::Named(_)) if self.module_origin(id) == Some(ModuleOrigin::PrimitivePrelude) => {
                String::new()
            }
            Some(ModuleKey::Named(name)) => name.dotted(),
        }
    }

    pub(crate) fn render_mfa(&self, key: &Mfa) -> String {
        let owner = self.module_display_name(key.module_id);
        if owner.is_empty() {
            key.function_name.clone()
        } else {
            format!("{owner}.{}", key.function_name)
        }
    }

    pub(crate) fn begin_lowering_extern_table(&self) -> ExternTable {
        ExternTable::from_decls(&self.extern_decls)
    }

    pub(crate) fn begin_lowering_extern_decls(&self) -> Vec<ExternDecl> {
        self.extern_decls.clone()
    }

    pub(crate) fn next_extern_id(&self) -> u32 {
        self.extern_decls.len() as u32
    }

    pub(crate) fn commit_lowering_extern_decls(&mut self, decls: &[ExternDecl]) {
        for decl in decls {
            if let Some(existing_id) = self.extern_name_ids.get(&decl.fz_name).copied() {
                let existing = &self.extern_decls[existing_id.0 as usize];
                assert_eq!(
                    existing.id, decl.id,
                    "extern `{}` changed ids across lowering sessions: existing {:?}, new {:?}",
                    decl.fz_name, existing.id, decl.id
                );
                assert!(
                    extern_decl_eq(existing, decl),
                    "extern `{}` declaration conflict across lowering sessions",
                    decl.fz_name
                );
                continue;
            }

            let expected = ExternId(self.extern_decls.len() as u32);
            assert_eq!(
                decl.id, expected,
                "compiler extern registry must append contiguous ids; expected {:?}, got {:?}",
                expected, decl.id
            );
            self.extern_name_ids.insert(decl.fz_name.clone(), decl.id);
            self.extern_decls.push(decl.clone());
        }
    }

    fn reserve_named_function_entity(
        &mut self,
        owner_module_id: ModuleId,
        mfa: Mfa,
        debug_name: impl Into<String>,
    ) -> FnId {
        if let Some(existing) = self.named_function_ids.get(&mfa).copied() {
            return existing;
        }
        let id = FnId(self.functions.len() as u32);
        self.named_function_ids.insert(mfa.clone(), id);
        self.named_function_keys.insert(id, mfa.clone());
        self.functions.push(FunctionRecord {
            id,
            owner_module_id,
            key: FunctionKey::Named(mfa),
            kind: FunctionKind::Source,
            debug_name: debug_name.into(),
            contract_state: FunctionContractState::Referenced,
            declared_extern: None,
            declared_source_specs: Vec::new(),
            declared_interface_specs: Vec::new(),
        });
        id
    }

    fn reserve_anonymous_function_entity(
        &mut self,
        owner_module_id: ModuleId,
        kind: FunctionKind,
        debug_name: impl Into<String>,
    ) -> FnId {
        let id = FnId(self.functions.len() as u32);
        let anonymous_id = AnonymousFunctionId(self.next_anonymous_function_id);
        self.next_anonymous_function_id += 1;
        self.functions.push(FunctionRecord {
            id,
            owner_module_id,
            key: FunctionKey::Anonymous(anonymous_id),
            kind,
            debug_name: debug_name.into(),
            contract_state: FunctionContractState::Referenced,
            declared_extern: None,
            declared_source_specs: Vec::new(),
            declared_interface_specs: Vec::new(),
        });
        id
    }

    pub(crate) fn fn_id_for_mfa(&self, mfa: &Mfa) -> Option<FnId> {
        self.named_function_ids.get(mfa).copied()
    }

    pub(crate) fn mfa_for_fn_id(&self, fn_id: FnId) -> Option<&Mfa> {
        self.named_function_keys.get(&fn_id)
    }

    pub(crate) fn function_contract_state(&self, mfa: &Mfa) -> Option<FunctionContractState> {
        let fn_id = self.fn_id_for_mfa(mfa)?;
        Some(self.function(fn_id).contract_state)
    }

    pub(crate) fn reference_fn(&mut self, mfa: Mfa) -> FnId {
        let debug_name = self.render_mfa(&mfa);
        self.reserve_named_function_entity(mfa.module_id, mfa, debug_name)
    }

    pub(crate) fn declare_fn(&mut self, mfa: Mfa, is_public: bool) -> FnId {
        let fn_id = self.reference_fn(mfa.clone());
        let rendered = self.render_mfa(&mfa);
        let record = &mut self.functions[fn_id.0 as usize];
        assert_eq!(
            record.owner_module_id, mfa.module_id,
            "function declaration owner conflict for `{}`",
            rendered
        );
        record.kind = FunctionKind::Source;
        if matches!(record.contract_state, FunctionContractState::Referenced) {
            record.contract_state = FunctionContractState::Declared;
        }
        if is_public {
            self.record_visible_callable(
                mfa.module_id,
                mfa.function_name.clone(),
                mfa.arity,
                mfa,
                VisibleCallableAliasOrigin::SourceDeclaration,
            );
        }
        fn_id
    }

    pub(crate) fn declare_extern_fn(&mut self, mfa: Mfa, decl: ExternFunctionDecl, is_public: bool) -> FnId {
        let fn_id = self.declare_fn(mfa.clone(), is_public);
        let rendered = self.render_mfa(&mfa);
        let record = &mut self.functions[fn_id.0 as usize];
        if let Some(existing) = &record.declared_extern {
            assert_eq!(
                existing, &decl,
                "extern function declaration conflict for `{}`",
                rendered
            );
        } else {
            record.declared_extern = Some(decl);
        }
        fn_id
    }

    pub(crate) fn declare_anonymous_fn(
        &mut self,
        owner_module_id: ModuleId,
        kind: FunctionKind,
        debug_name: impl Into<String>,
    ) -> FnId {
        let fn_id = self.reserve_anonymous_function_entity(owner_module_id, kind, debug_name);
        self.functions[fn_id.0 as usize].contract_state = FunctionContractState::Declared;
        fn_id
    }

    pub(crate) fn visible_callable_target(&self, module_id: ModuleId, name: &str, arity: usize) -> Option<Mfa> {
        self.visible_callable_target_in_namespace(self.module(module_id).namespace_id, name, arity)
    }

    pub(crate) fn visible_callable_aliases(&self, module_id: ModuleId) -> Vec<VisibleCallableAlias> {
        let mut aliases = self
            .namespace(self.module(module_id).namespace_id)
            .callable_bindings
            .values()
            .cloned()
            .collect::<Vec<_>>();
        aliases.sort_by(|left, right| {
            (&left.name, left.arity, self.render_mfa(&left.target)).cmp(&(
                &right.name,
                right.arity,
                self.render_mfa(&right.target),
            ))
        });
        aliases
    }

    fn primitive_prelude_import_map(&self, module_id: ModuleId) -> HashMap<(String, usize), String> {
        self.visible_callable_aliases(module_id)
            .into_iter()
            .map(|alias| ((alias.name, alias.arity), self.render_mfa(&alias.target)))
            .collect()
    }

    pub(crate) fn visible_module_binding_target(&self, module_id: ModuleId, name: &str) -> Option<ModuleId> {
        self.visible_module_binding_target_in_namespace(self.module(module_id).namespace_id, name)
    }

    pub(crate) fn resolve_module(&mut self, namespace_id: NamespaceId, name: &ModuleName) -> ModuleId {
        if let Some(mut current_module_id) = self.visible_module_binding_target_in_namespace(
            namespace_id,
            name.segments().first().map(String::as_str).unwrap_or_default(),
        ) {
            for segment in name.segments().iter().skip(1) {
                let Some(next_module_id) = self.visible_module_binding_target(current_module_id, segment) else {
                    return self.reference_named_module(name.clone(), &crate::telemetry::NullTelemetry);
                };
                current_module_id = next_module_id;
            }
            return current_module_id;
        }
        self.reference_named_module(name.clone(), &crate::telemetry::NullTelemetry)
    }

    pub(crate) fn module_contract(&self, module_id: ModuleId) -> Option<&ModuleContractRecord> {
        self.module(module_id).contract.as_ref()
    }

    pub(crate) fn module_contract_for_name(&self, module: &ModuleName) -> Option<&ModuleContractRecord> {
        let module_id = self.module_id_for_name(module)?;
        self.module_contract(module_id)
    }

    pub(crate) fn function_declared_interface_specs(&self, mfa: &Mfa) -> Option<&[InterfaceSpec]> {
        let fn_id = self.fn_id_for_mfa(mfa)?;
        let specs = self.function(fn_id).declared_interface_specs.as_slice();
        (!specs.is_empty()).then_some(specs)
    }

    pub(crate) fn function_declared_source_specs(&self, mfa: &Mfa) -> Option<&[SpecDecl]> {
        let fn_id = self.fn_id_for_mfa(mfa)?;
        let specs = self.function(fn_id).declared_source_specs.as_slice();
        (!specs.is_empty()).then_some(specs)
    }

    pub(crate) fn ensure_function_contract_state(
        &mut self,
        mfa: &Mfa,
        tel: &dyn Telemetry,
    ) -> Result<Option<FunctionContractState>, Diagnostic> {
        let mut fn_id = self.fn_id_for_mfa(mfa);
        if fn_id.is_none() {
            let _ = self.ensure_body_surface(mfa.module_id, tel)?;
            fn_id = self.fn_id_for_mfa(mfa);
        }
        let Some(fn_id) = fn_id else {
            return Ok(None);
        };
        let owner_module_id = self.function(fn_id).owner_module_id;
        let state = self.function(fn_id).contract_state;
        if matches!(state, FunctionContractState::SourceAndInterfaceReady) {
            return Ok(Some(state));
        }
        let _ = self.ensure_body_surface(owner_module_id, tel)?;
        if !matches!(
            self.function(fn_id).contract_state,
            FunctionContractState::InterfaceReady | FunctionContractState::SourceAndInterfaceReady
        ) && matches!(self.module(owner_module_id).key, Some(ModuleKey::Named(_)))
        {
            let _ = self.ensure_interface_table(owner_module_id, tel)?;
        }
        Ok(Some(self.function(fn_id).contract_state))
    }

    pub(crate) fn record_visible_callable_alias(
        &mut self,
        module_id: ModuleId,
        name: String,
        arity: usize,
        target: Mfa,
        origin: VisibleCallableAliasOrigin,
    ) {
        self.record_visible_callable(module_id, name, arity, target, origin);
    }

    pub(crate) fn set_namespace_parent(&mut self, module_id: ModuleId, parent_module_id: ModuleId) {
        let namespace_id = self.module(module_id).namespace_id;
        let parent_namespace_id = self.module(parent_module_id).namespace_id;
        let namespace = self.namespace_mut(namespace_id);
        if let Some(existing_parent) = namespace.parent {
            assert_eq!(
                existing_parent,
                parent_namespace_id,
                "namespace parent conflict for module `{}`",
                self.module_key_render(module_id)
            );
            return;
        }
        namespace.parent = Some(parent_namespace_id);
    }

    fn record_visible_callable(
        &mut self,
        module_id: ModuleId,
        name: String,
        arity: usize,
        target: Mfa,
        origin: VisibleCallableAliasOrigin,
    ) {
        let key = (name, arity);
        let namespace_id = self.module(module_id).namespace_id;
        if let Some(existing) = self.namespace(namespace_id).callable_bindings.get(&key) {
            assert_eq!(
                (existing.target.clone(), existing.origin.clone()),
                (target.clone(), origin.clone()),
                "visible callable conflict for module `{}` alias `{}/{}': existing target `{}` ({}), new target `{}` ({})",
                self.module_key_render(module_id),
                key.0,
                key.1,
                self.render_mfa(&existing.target),
                existing.origin.kind(),
                self.render_mfa(&target),
                origin.kind(),
            );
            return;
        }
        self.namespace_mut(namespace_id).callable_bindings.insert(
            key.clone(),
            VisibleCallableAlias {
                name: key.0.clone(),
                arity: key.1,
                target,
                origin,
            },
        );
    }

    pub(crate) fn record_visible_module_binding(
        &mut self,
        module_id: ModuleId,
        name: String,
        target_module_id: ModuleId,
        origin: VisibleModuleBindingOrigin,
    ) {
        let namespace_id = self.module(module_id).namespace_id;
        if let Some(existing) = self.namespace(namespace_id).module_bindings.get(&name) {
            assert_eq!(
                (existing.target_module_id, existing.origin.clone()),
                (target_module_id, origin.clone()),
                "visible module binding conflict for module `{}` alias `{}`",
                self.module_key_render(module_id),
                name,
            );
            return;
        }
        self.namespace_mut(namespace_id).module_bindings.insert(
            name.clone(),
            VisibleModuleBinding {
                name,
                target_module_id,
                origin,
            },
        );
    }

    fn visible_callable_target_in_namespace(&self, namespace_id: NamespaceId, name: &str, arity: usize) -> Option<Mfa> {
        let namespace = self.namespace(namespace_id);
        if let Some(alias) = namespace.callable_bindings.get(&(name.to_string(), arity)) {
            return Some(alias.target.clone());
        }
        let parent = namespace.parent?;
        self.visible_callable_target_in_namespace(parent, name, arity)
    }

    fn visible_module_binding_target_in_namespace(&self, namespace_id: NamespaceId, name: &str) -> Option<ModuleId> {
        let namespace = self.namespace(namespace_id);
        if let Some(binding) = namespace.module_bindings.get(name) {
            return Some(binding.target_module_id);
        }
        let parent = namespace.parent?;
        self.visible_module_binding_target_in_namespace(parent, name)
    }

    fn record_function_source_specs(&mut self, mfa: &Mfa, specs: &[SpecDecl]) {
        let Some(fn_id) = self.fn_id_for_mfa(mfa) else {
            return;
        };
        let rendered = self.render_mfa(mfa);
        let record = &mut self.functions[fn_id.0 as usize];
        if record.declared_source_specs.is_empty() {
            record.declared_source_specs = specs.to_vec();
            record.contract_state = match record.contract_state {
                FunctionContractState::Referenced => FunctionContractState::SourceReady,
                FunctionContractState::Declared => FunctionContractState::SourceReady,
                FunctionContractState::InterfaceReady => FunctionContractState::SourceAndInterfaceReady,
                state => state,
            };
            return;
        }
        assert_eq!(
            record.declared_source_specs, specs,
            "source function contract conflict for `{}`",
            rendered
        );
    }

    fn record_function_interface_specs(&mut self, mfa: &Mfa, specs: &[InterfaceSpec]) {
        let Some(fn_id) = self.fn_id_for_mfa(mfa) else {
            return;
        };
        let rendered = self.render_mfa(mfa);
        let record = &mut self.functions[fn_id.0 as usize];
        if record.declared_interface_specs.is_empty() {
            record.declared_interface_specs = specs.to_vec();
            record.contract_state = match record.contract_state {
                FunctionContractState::Referenced => FunctionContractState::InterfaceReady,
                FunctionContractState::Declared => FunctionContractState::InterfaceReady,
                FunctionContractState::SourceReady => FunctionContractState::SourceAndInterfaceReady,
                state => state,
            };
            return;
        }
        assert_eq!(
            record.declared_interface_specs, specs,
            "function contract conflict for `{}`",
            rendered
        );
    }

    pub(crate) fn named_surface_entries_for_files(
        &self,
        file_ids: &HashSet<FileId>,
    ) -> Vec<crate::fz_ir::NamedFnSurfaceEntry> {
        let mut entries = Vec::new();
        for module in &self.modules {
            let Some(file_id) = module.file_id() else {
                continue;
            };
            if !file_ids.contains(&file_id) {
                continue;
            }
            for target in self.namespace(module.namespace_id).callable_bindings.values() {
                let mfa = target.target.clone();
                let Some(fn_id) = self.fn_id_for_mfa(&mfa) else {
                    continue;
                };
                entries.push(crate::fz_ir::NamedFnSurfaceEntry {
                    name: self.render_mfa(&mfa),
                    arity: mfa.arity,
                    fn_id,
                });
            }
        }
        entries.sort_by(|a, b| (&a.name, a.arity, a.fn_id.0).cmp(&(&b.name, b.arity, b.fn_id.0)));
        entries
            .dedup_by(|left, right| left.name == right.name && left.arity == right.arity && left.fn_id == right.fn_id);
        entries
    }

    fn record_module_contract(
        &mut self,
        module_id: ModuleId,
        interface: ModuleInterface,
        origin: ModuleContractOrigin,
    ) {
        let rendered_module = interface.name.to_string();
        for export in &interface.exports {
            let mfa = Mfa::new(module_id, export.name.clone(), export.arity);
            self.reserve_named_function_entity(module_id, mfa.clone(), format!("{}.{}", rendered_module, export.name));
            self.record_function_interface_specs(&mfa, &export.specs);
        }
        let record = &mut self.modules[module_id.0 as usize];
        if let Some(existing) = &record.contract {
            assert_eq!(
                existing.interface, interface,
                "module contract conflict for `{}`",
                rendered_module
            );
            assert_eq!(
                existing.origin, origin,
                "module contract origin conflict for `{}`",
                rendered_module
            );
            return;
        }
        record.contract = Some(ModuleContractRecord { interface, origin });
    }

    pub(crate) fn source_fn_key_for_qualified_name(
        &self,
        default_module_id: ModuleId,
        qualified_name: &str,
        arity: usize,
    ) -> Result<SourceFnKey, Diagnostic> {
        if let Some((module_prefix, function_name)) = qualified_name.rsplit_once('.') {
            let module = ModuleName::parse_dotted(module_prefix).map_err(|err| {
                Diagnostic::error(
                    crate::diag::codes::LOWER_UNBOUND,
                    format!("invalid qualified function name `{qualified_name}`: {err}"),
                    Span::DUMMY,
                )
            })?;
            let module_id = self.module_id_for_name(&module).ok_or_else(|| {
                Diagnostic::error(
                    crate::diag::codes::LOWER_UNBOUND,
                    format!("unknown source module `{module}` for `{qualified_name}`"),
                    Span::DUMMY,
                )
            })?;
            Ok(SourceFnKey::new(module_id, function_name.to_string(), arity))
        } else {
            Ok(SourceFnKey::new(default_module_id, qualified_name.to_string(), arity))
        }
    }

    pub(crate) fn lower_program_from_demands<T: crate::types::Types<Ty = crate::types::Ty>>(
        &mut self,
        root_source: Option<ModuleId>,
        t: &mut T,
        prog: &Program,
        tel: &dyn Telemetry,
    ) -> Result<crate::fz_ir::Module, LowerError> {
        let mut session = begin_compiler_lowering_session(self, root_source, t, prog, tel)?;
        let initial_demands = if let Some(root_source) = root_source
            && self.module_origin(root_source) != Some(ModuleOrigin::PrimitivePrelude)
        {
            let runtime_entry_keys = self.runtime_entry_fn_keys(root_source);
            let root_entry_keys = (!runtime_entry_keys.is_empty()).then_some(&runtime_entry_keys);
            let surface = self
                .ensure_body_surface(root_source, tel)
                .map_err(|diagnostic| LowerError::Unsupported {
                    span: Span::DUMMY,
                    what: diagnostic.message,
                })?;
            select_initial_root_fn_keys(&surface, root_entry_keys)
        } else {
            collect_lowerable_fn_keys(self, session.user_root_module_id, &prog.items)
        };

        if let Some(root_source) = root_source {
            for fn_key in &initial_demands {
                if let Some(descriptor) = self
                    .source_fn_group_descriptor_for_key(root_source, fn_key, tel)
                    .map_err(|diagnostic| LowerError::Unsupported {
                        span: Span::DUMMY,
                        what: diagnostic.message,
                    })?
                {
                    tel.execute(
                        &["fz", "compiler", "fn_group_seeded"],
                        &measurements! {
                            fn_group_id: descriptor.id.0,
                            loaded_functions: 0_u64,
                        },
                        &metadata! {
                            module_key: self.module_key_render(root_source),
                            owner_module: self.module_display_name(descriptor.source.module_id),
                            fn_name: descriptor.qualified_name(),
                        },
                    );
                }
            }
        }

        let mut demands = initial_demands.into_iter().collect::<VecDeque<FnKey>>();
        let mut satisfied = HashSet::new();
        while let Some(fn_key) = demands.pop_front() {
            if !satisfied.insert(fn_key.clone()) {
                continue;
            }
            match session.satisfy_fn_group_demand(self, t, tel, &fn_key, &satisfied) {
                LoweringDemandResult::Finished => {}
                LoweringDemandResult::Demands(new_demands) => {
                    for demand in new_demands {
                        if !satisfied.contains(&demand) {
                            demands.push_back(demand);
                        }
                    }
                }
                LoweringDemandResult::Fatal(err) => return Err(err),
            }
        }
        session.finish(self, t, prog, tel)
    }

    fn contract_table_for_modules(&self, modules: &BTreeSet<ModuleName>) -> InterfaceTable {
        let mut out = InterfaceTable::new();
        for module in modules {
            if let Some(contract) = self.module_contract_for_name(module) {
                out.insert(module.clone(), contract.interface.clone());
            }
        }
        out
    }

    fn satisfy_module_contract_demand(
        &mut self,
        request: &ModuleContractRequest,
        tel: &dyn Telemetry,
    ) -> Result<BTreeSet<ModuleName>, Diagnostic> {
        let mut resolved = BTreeSet::new();
        let mut queue = VecDeque::from([request.target_module.clone()]);
        while let Some(module_name) = queue.pop_front() {
            if !resolved.insert(module_name.clone()) {
                continue;
            }
            if self.module_contract_for_name(&module_name).is_none() {
                let prelude_id = self.discover_primitive_prelude(tel);
                self.ensure_primitive_prelude_namespace(prelude_id, tel)?;
            }
            if self.module_contract_for_name(&module_name).is_none() {
                let Some(interface) = self.ensure_runtime_module_interface(&module_name, tel)? else {
                    return Err(Diagnostic::error(
                        crate::diag::codes::RESOLVE_UNKNOWN_MODULE,
                        format!("module `{}` is not defined", module_name),
                        request.span,
                    ));
                };
                if let Some(module_id) = self.module_id_for_name(&module_name) {
                    self.record_module_contract(
                        module_id,
                        interface,
                        ModuleContractOrigin::CompilerOwned(self.declared_module_origin(module_id)),
                    );
                }
            }
            let Some(contract) = self.module_contract_for_name(&module_name) else {
                return Err(Diagnostic::error(
                    crate::diag::codes::RESOLVE_UNKNOWN_MODULE,
                    format!("module `{}` is not defined", module_name),
                    request.span,
                ));
            };
            for import in &contract.interface.imports {
                queue.push_back(import.module.clone());
            }
            for protocol_impl in &contract.interface.protocol_impls {
                queue.push_back(protocol_impl.protocol.clone());
            }
        }
        Ok(resolved)
    }

    pub(crate) fn resolve_program_from_demands<T: Types<Ty = Ty>>(
        &mut self,
        t: &mut T,
        root_source: Option<ModuleId>,
        prog: Program,
        interface_table: InterfaceTable,
        tel: &dyn Telemetry,
    ) -> Result<Program, Diagnostic> {
        let local_interfaces = match root_source {
            Some(root_source) => self.ensure_source_module_interfaces(root_source, tel)?,
            None => collect_from_program(&prog),
        };
        self.record_supplemental_module_contracts(&interface_table, tel);
        let mut external_modules = interface_table.keys().cloned().collect::<BTreeSet<_>>();
        loop {
            let external_interfaces = self.contract_table_for_modules(&external_modules);
            match resolve_program_once(
                t,
                self,
                root_source,
                prog.clone(),
                local_interfaces.clone(),
                external_interfaces,
                tel,
            ) {
                ResolveDemandResult::Finished(program) => return Ok(program),
                ResolveDemandResult::Demands(demands) => {
                    for demand in demands {
                        external_modules.extend(self.satisfy_module_contract_demand(&demand, tel)?);
                    }
                }
                ResolveDemandResult::Fatal(diagnostic) => return Err(diagnostic),
            }
        }
    }

    pub(crate) fn compile_program_from_roots<T>(
        &mut self,
        root_source: Option<ModuleId>,
        lowering_root_source: Option<ModuleId>,
        t: &mut T,
        prog: Program,
        sm: SourceMap,
        interface_table: InterfaceTable,
        tel: &dyn Telemetry,
    ) -> FrontendResult
    where
        T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes,
    {
        let mut prog = match self.resolve_program_from_demands(t, root_source, prog, interface_table, tel) {
            Ok(prog) => prog,
            Err(diagnostic) => {
                return Err(FrontendErr {
                    sm,
                    diagnostics: crate::diag::Diagnostics::from_one(diagnostic),
                });
            }
        };
        tel.event(
            &["fz", "frontend", "resolved"],
            metadata! {
                items: prog.items.len(),
                module_interfaces: prog.module_interfaces.len(),
                program: opaque(&prog),
            },
        );
        if let Err(diagnostic) = macros::prepare_compiler_macro_surfaces(self, root_source, &prog, tel) {
            return Err(FrontendErr {
                sm,
                diagnostics: crate::diag::Diagnostics::from_one(diagnostic),
            });
        }
        if let Err(err) = macros::expand_program_with_compiler_types(self, root_source, t, &mut prog) {
            return Err(FrontendErr {
                sm,
                diagnostics: crate::diag::Diagnostics::from_one(err.to_diagnostic()),
            });
        }
        resolve::add_macro_requested_runtime_interfaces(self, &mut prog, tel);
        tel.event(
            &["fz", "frontend", "macro_expanded"],
            metadata! {
                items: prog.items.len(),
                program: opaque(&prog),
            },
        );
        let mut module = match self.lower_program_from_demands(lowering_root_source, t, &prog, tel) {
            Ok(module) => module,
            Err(err) => {
                return Err(FrontendErr {
                    sm,
                    diagnostics: crate::diag::Diagnostics::from_one(err.to_diagnostic()),
                });
            }
        };
        tel.event(
            &["fz", "frontend", "lowered"],
            metadata! {
                module_path: module.module_path().to_owned(),
                fns: module.fns.len(),
                module: opaque(&module),
            },
        );
        let planner_entry_fns = planner_entry_fns(self, lowering_root_source, &module);
        let validate_surface = validate_surface_for_plan(self, lowering_root_source, &planner_entry_fns);
        let (diagnostics, mut module_plan) =
            check_frontend_from_entry_fns(t, &prog, &module, &planner_entry_fns, validate_surface, tel);
        apply_planner_rewrites_to_fixed_point(t, &mut module, &mut module_plan, &planner_entry_fns);
        if let Some(module_id) = lowering_root_source
            && self.module_origin(module_id) == Some(ModuleOrigin::EmbeddedRuntime)
        {
            self.finish_runtime_module_compilation(module_id, module.fns.len(), module_plan.specs.len(), tel);
        }
        #[cfg(test)]
        self.validate_invariants()
            .expect("frontend compile must leave compiler world consistent");
        Ok(FrontendOk {
            sm,
            _prog: prog,
            module,
            module_plan,
            diagnostics,
        })
    }
}

fn extern_decl_eq(left: &ExternDecl, right: &ExternDecl) -> bool {
    left.id == right.id
        && left.fz_name == right.fz_name
        && left.symbol == right.symbol
        && left.params == right.params
        && left.variadic == right.variadic
        && left.ret == right.ret
        && left.ret_descr == right.ret_descr
}

impl Compiler {
    pub(crate) fn new() -> Self {
        Self {
            types: types::new(),
            world: CompilerWorld::new(),
        }
    }

    pub(crate) fn types(&mut self) -> &mut DefaultTypes {
        &mut self.types
    }

    pub(crate) fn split_mut(&mut self) -> (&mut DefaultTypes, &mut CompilerWorld) {
        (&mut self.types, &mut self.world)
    }

    pub(crate) fn world_mut(&mut self) -> &mut CompilerWorld {
        &mut self.world
    }

    pub(crate) fn world(&self) -> &CompilerWorld {
        &self.world
    }

    pub(crate) fn module_count(&self) -> usize {
        self.world.module_count()
    }

    pub(crate) fn file_count(&self) -> usize {
        self.world.file_count()
    }

    pub(crate) fn function_count(&self) -> usize {
        self.world.function_count()
    }

    pub(crate) fn module(&self, id: ModuleId) -> &ModuleRecord {
        self.world.module(id)
    }

    pub(crate) fn file(&self, id: FileId) -> &FileRecord {
        self.world.file(id)
    }

    pub(crate) fn function(&self, id: FnId) -> &FunctionRecord {
        self.world.function(id)
    }

    pub(crate) fn register_root_source(
        &mut self,
        path: impl AsRef<Path>,
        src: String,
        tel: &dyn Telemetry,
    ) -> ModuleId {
        self.world.register_root_source(path, src, tel)
    }

    pub(crate) fn discover_runtime_module(&mut self, module: &ModuleName, tel: &dyn Telemetry) -> Option<ModuleId> {
        self.world.discover_runtime_module(module, tel)
    }

    pub(crate) fn discover_primitive_prelude(&mut self, tel: &dyn Telemetry) -> ModuleId {
        self.world.discover_primitive_prelude(tel)
    }

    pub(crate) fn module_id_for_name(&self, module: &ModuleName) -> Option<ModuleId> {
        self.world.module_id_for_name(module)
    }

    pub(crate) fn fn_id_for_mfa(&self, mfa: &Mfa) -> Option<FnId> {
        self.world.fn_id_for_mfa(mfa)
    }

    pub(crate) fn reference_fn(&mut self, mfa: Mfa) -> FnId {
        self.world.reference_fn(mfa)
    }

    pub(crate) fn declare_fn(&mut self, mfa: Mfa, is_public: bool) -> FnId {
        self.world.declare_fn(mfa, is_public)
    }

    pub(crate) fn declare_extern_fn(&mut self, mfa: Mfa, decl: ExternFunctionDecl, is_public: bool) -> FnId {
        self.world.declare_extern_fn(mfa, decl, is_public)
    }

    pub(crate) fn declare_anonymous_fn(
        &mut self,
        owner_module_id: ModuleId,
        kind: FunctionKind,
        debug_name: impl Into<String>,
    ) -> FnId {
        self.world.declare_anonymous_fn(owner_module_id, kind, debug_name)
    }

    pub(crate) fn ensure_source(&mut self, module_id: ModuleId, tel: &dyn Telemetry) -> Arc<str> {
        self.world.ensure_source(module_id, tel)
    }

    pub(crate) fn ensure_parsed(
        &mut self,
        module_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<ParsedSource, Diagnostic> {
        self.world.ensure_parsed(module_id, tel)
    }

    pub(crate) fn ensure_program(
        &mut self,
        module_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<ParsedProgram, Diagnostic> {
        self.world.ensure_program(module_id, tel)
    }

    pub(crate) fn ensure_prelude(
        &mut self,
        module_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<ParsedPrelude, Diagnostic> {
        self.world.ensure_prelude(module_id, tel)
    }

    pub(crate) fn ensure_prepared_prelude(
        &mut self,
        module_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<PreparedPrelude, Diagnostic> {
        self.world.ensure_prepared_prelude(module_id, &mut self.types, tel)
    }

    pub(crate) fn ensure_primitive_prelude_namespace(
        &mut self,
        module_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<(), Diagnostic> {
        self.world.ensure_primitive_prelude_namespace(module_id, tel)
    }

    pub(crate) fn ensure_interface_table(
        &mut self,
        module_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<BTreeMap<ModuleName, ModuleInterface>, Diagnostic> {
        self.world.ensure_interface_table(module_id, tel)
    }

    pub(crate) fn ensure_body_surface(
        &mut self,
        module_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<ModuleBodySurface, Diagnostic> {
        self.world.ensure_body_surface(module_id, tel)
    }

    pub(crate) fn source_fn_group_descriptor(
        &mut self,
        module_id: ModuleId,
        name: &str,
        arity: usize,
        tel: &dyn Telemetry,
    ) -> Result<Option<FnGroupDescriptor>, Diagnostic> {
        self.world.source_fn_group_descriptor(module_id, name, arity, tel)
    }

    pub(crate) fn source_fn_group_descriptor_for_key(
        &mut self,
        module_id: ModuleId,
        key: &SourceFnKey,
        tel: &dyn Telemetry,
    ) -> Result<Option<FnGroupDescriptor>, Diagnostic> {
        self.world.source_fn_group_descriptor_for_key(module_id, key, tel)
    }

    pub(crate) fn ensure_runtime_module_interface(
        &mut self,
        module: &ModuleName,
        tel: &dyn Telemetry,
    ) -> Result<Option<ModuleInterface>, Diagnostic> {
        self.world.ensure_runtime_module_interface(module, tel)
    }

    pub(crate) fn ensure_source_module_interfaces(
        &mut self,
        root_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<BTreeMap<ModuleName, ModuleInterface>, Diagnostic> {
        self.world.ensure_source_module_interfaces(root_id, tel)
    }

    pub(crate) fn ensure_source_module_macro_exports(
        &mut self,
        root_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<SourceMacroExports, Diagnostic> {
        self.world.ensure_source_module_macro_exports(root_id, tel)
    }

    pub(crate) fn discover_runtime_reachable_modules(
        &mut self,
        root_interfaces: &BTreeMap<ModuleName, ModuleInterface>,
        seeds: impl IntoIterator<Item = RuntimeReachabilitySeed>,
        tel: &dyn Telemetry,
    ) -> Result<Vec<ModuleId>, Diagnostic> {
        self.world
            .discover_runtime_reachable_modules(root_interfaces, seeds, tel)
    }

    pub(crate) fn mark_reachable(&mut self, module_id: ModuleId, kind: ReachabilityKind, tel: &dyn Telemetry) -> bool {
        self.world.mark_reachable(module_id, kind, tel)
    }

    pub(crate) fn validate_invariants(&self) -> Result<(), CompilerInvariantError> {
        self.world.validate_invariants()
    }

    pub(crate) fn ensure_module_readiness<F>(
        &mut self,
        module_id: ModuleId,
        fact: ModuleReadinessFact,
        tel: &dyn Telemetry,
        work: F,
    ) -> bool
    where
        F: FnOnce(&mut CompilerWorld),
    {
        self.world.ensure_module_readiness(module_id, fact, tel, work)
    }

    pub(crate) fn ensure_module_readiness_result<F, E>(
        &mut self,
        module_id: ModuleId,
        fact: ModuleReadinessFact,
        tel: &dyn Telemetry,
        work: F,
    ) -> Result<bool, E>
    where
        F: FnOnce(&mut CompilerWorld) -> Result<(), E>,
    {
        self.world.ensure_module_readiness_result(module_id, fact, tel, work)
    }
}

fn planner_entry_fns(
    compiler: &CompilerWorld,
    lowering_root_source: Option<ModuleId>,
    module: &crate::fz_ir::Module,
) -> Vec<FnId> {
    let Some(root_source) = lowering_root_source else {
        return Vec::new();
    };
    if compiler.module_origin(root_source) != Some(ModuleOrigin::EmbeddedRuntime) {
        return Vec::new();
    }
    let entry_keys = compiler.runtime_entry_fn_keys(root_source);
    if entry_keys.is_empty() {
        return Vec::new();
    }
    entry_keys
        .into_iter()
        .filter_map(|mfa| compiler.fn_id_for_mfa(&mfa))
        .filter(|fn_id| module.fn_idx.contains_key(fn_id))
        .collect()
}

fn validate_surface_for_plan(
    compiler: &CompilerWorld,
    lowering_root_source: Option<ModuleId>,
    planner_entry_fns: &[FnId],
) -> bool {
    let Some(root_source) = lowering_root_source else {
        return true;
    };
    compiler.module_origin(root_source) != Some(ModuleOrigin::EmbeddedRuntime) || planner_entry_fns.is_empty()
}

fn apply_planner_rewrites_to_fixed_point<T>(
    t: &mut T,
    module: &mut crate::fz_ir::Module,
    module_plan: &mut ModulePlan,
    entry_fn_ids: &[FnId],
) where
    T: Types<Ty = Ty> + ClosureTypes + RenderTypes,
{
    loop {
        let direct_changed = apply_planned_direct_call_targets(module, module_plan);
        let switch_changed = rewrite_closed_union_protocol_dispatch(t, module, module_plan);
        if !(direct_changed || switch_changed) {
            break;
        }
        *module_plan = if entry_fn_ids.is_empty() {
            plan_module(t, module, &NullTelemetry)
        } else {
            plan_module_from_entry_fns(t, module, entry_fn_ids, &NullTelemetry)
        };
    }
}

impl CompilerWorld {
    pub(crate) fn reference_named_module(&mut self, module: ModuleName, tel: &dyn Telemetry) -> ModuleId {
        if let Some(existing) = self.module_index.get(&ModuleKey::Named(module.clone())).copied() {
            let record = self.module(existing);
            tel.execute(
                &["fz", "compiler", "module_cache_hit"],
                &measurements! { module_id: existing.0, file_id: record.file_id().map_or(u64::MAX as u32, |id| id.0) },
                &metadata! {
                    module_key: record.key_render(),
                    module_key_kind: record.key_kind(),
                    module_origin: self.module_origin_kind(existing),
                },
            );
            return existing;
        }
        let id = self.create_module_record(Some(ModuleKey::Named(module)), None, tel);
        id
    }

    pub(crate) fn register_root_source(
        &mut self,
        path: impl AsRef<Path>,
        src: String,
        tel: &dyn Telemetry,
    ) -> ModuleId {
        let path = path.as_ref().to_path_buf();
        self.declare_module(
            Some(ModuleKey::RootPath(path.clone())),
            ModuleOrigin::RootSource,
            FileOrigin::Filesystem(path.clone()),
            SourceDescriptor {
                source_name: path.display().to_string(),
                text: Arc::<str>::from(src),
                parse_kind: ParseKind::Program,
            },
            tel,
        )
    }

    pub(crate) fn register_anonymous_root_module(&mut self, label: impl Into<String>, tel: &dyn Telemetry) -> ModuleId {
        let label = label.into();
        let ordinal = self.modules.len();
        self.declare_module(
            None,
            ModuleOrigin::RootSource,
            FileOrigin::Synthetic(format!("anonymous:{label}:{ordinal}")),
            SourceDescriptor {
                source_name: format!("anonymous:{label}:{ordinal}"),
                text: Arc::<str>::from(""),
                parse_kind: ParseKind::Program,
            },
            tel,
        )
    }

    pub(crate) fn discover_runtime_module(&mut self, module: &ModuleName, tel: &dyn Telemetry) -> Option<ModuleId> {
        let source = RUNTIME_MODULE_SOURCES
            .iter()
            .find(|candidate| candidate.name == module.dotted())?;
        Some(self.declare_module(
            Some(ModuleKey::Named(module.clone())),
            ModuleOrigin::EmbeddedRuntime,
            FileOrigin::EmbeddedRuntime(source.name.to_string()),
            SourceDescriptor {
                source_name: format!("runtime:{name}", name = source.name),
                text: Arc::<str>::from(source.source),
                parse_kind: ParseKind::Prelude,
            },
            tel,
        ))
    }

    pub(crate) fn discover_primitive_prelude(&mut self, tel: &dyn Telemetry) -> ModuleId {
        let module = ModuleName::from_segments(vec!["$Prelude".to_string()]);
        self.declare_module(
            Some(ModuleKey::Named(module)),
            ModuleOrigin::PrimitivePrelude,
            FileOrigin::PrimitivePrelude("runtime.fz".to_string()),
            SourceDescriptor {
                source_name: "runtime:prelude".to_string(),
                text: Arc::<str>::from(RUNTIME_PRELUDE_FZ),
                parse_kind: ParseKind::Prelude,
            },
            tel,
        )
    }

    pub(crate) fn module_id_for_name(&self, module: &ModuleName) -> Option<ModuleId> {
        self.module_index.get(&ModuleKey::Named(module.clone())).copied()
    }

    pub(crate) fn ensure_source(&mut self, module_id: ModuleId, tel: &dyn Telemetry) -> Arc<str> {
        let _ = self.ensure_module_readiness(module_id, ModuleReadinessFact::SourceReady, tel, |this| {
            let file_id = this.declared_module_file_id(module_id);
            let measurements = this.state_measurements(module_id);
            let module_key = this.module(module_id).key_render();
            let module_key_kind = this.module(module_id).key_kind();
            let module_origin = this.declared_module_origin(module_id).kind();
            let record = &mut this.files[file_id.0 as usize];
            let source = record.descriptor.text.clone();
            record.source = Some(source.clone());
            tel.execute(
                &["fz", "compiler", "source_loaded"],
                &measurements,
                &metadata! {
                    module_key: module_key,
                    module_key_kind: module_key_kind,
                    module_origin: module_origin,
                    source_name: record.descriptor.source_name.clone(),
                    file_origin: record.origin.kind(),
                    parse_kind: record.descriptor.parse_kind.as_str(),
                    bytes: source.len() as u64,
                },
            );
        });
        let file_id = self.declared_module_file_id(module_id);
        self.files[file_id.0 as usize]
            .source
            .clone()
            .expect("source_ready invariant violated")
    }

    pub(crate) fn ensure_parsed(
        &mut self,
        module_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<ParsedSource, Diagnostic> {
        self.ensure_module_readiness_result(module_id, ModuleReadinessFact::Parsed, tel, |this| {
            let file_id = this.declared_module_file_id(module_id);
            let source = this.ensure_source(module_id, tel);
            let descriptor = this.files[file_id.0 as usize].descriptor.clone();
            let parsed = parse_source(&descriptor, &source, tel)?;
            let measurements = this.state_measurements(module_id);
            tel.execute(
                &["fz", "compiler", "parsed"],
                &measurements,
                &metadata! {
                    module_key: this.module(module_id).key_render(),
                    module_key_kind: this.module(module_id).key_kind(),
                    module_origin: this.declared_module_origin(module_id).kind(),
                    source_name: descriptor.source_name.clone(),
                    parse_kind: parsed.parse_kind().as_str(),
                    items: parsed.item_count() as u64,
                },
            );
            this.files[file_id.0 as usize].parsed = Some(parsed);
            Ok(())
        })?;

        let file_id = self.declared_module_file_id(module_id);
        Ok(self.files[file_id.0 as usize]
            .parsed
            .clone()
            .expect("parsed invariant violated"))
    }

    pub(crate) fn ensure_program(
        &mut self,
        module_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<ParsedProgram, Diagnostic> {
        match self.ensure_parsed(module_id, tel)? {
            ParsedSource::Program(parsed) => Ok(parsed),
            ParsedSource::Prelude(_) => panic!("compiler source kind mismatch: expected program"),
        }
    }

    pub(crate) fn ensure_prelude(
        &mut self,
        module_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<ParsedPrelude, Diagnostic> {
        match self.ensure_parsed(module_id, tel)? {
            ParsedSource::Prelude(parsed) => Ok(parsed),
            ParsedSource::Program(_) => panic!("compiler source kind mismatch: expected prelude"),
        }
    }

    pub(crate) fn ensure_primitive_prelude_namespace(
        &mut self,
        module_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<(), Diagnostic> {
        self.ensure_module_readiness_result(module_id, ModuleReadinessFact::NamespaceReady, tel, |this| {
            let parsed = this.ensure_prelude(module_id, tel)?;
            record_runtime_prelude_namespace(this, module_id, tel, &parsed.items)?;
            this.emit_namespace_ready(module_id, tel);
            Ok(())
        })?;
        Ok(())
    }

    pub(crate) fn ensure_prepared_prelude<T: types::Types<Ty = types::Ty>>(
        &mut self,
        module_id: ModuleId,
        t: &mut T,
        tel: &dyn Telemetry,
    ) -> Result<PreparedPrelude, Diagnostic> {
        if let Some(prepared) = &self.modules[module_id.0 as usize].prepared_prelude {
            return Ok(prepared.clone());
        }

        let parsed = self.ensure_prelude(module_id, tel)?;
        self.ensure_primitive_prelude_namespace(module_id, tel)?;
        let root_types = runtime_library::root_type_env_from_attrs(t, &parsed.attrs);
        let imports = self.primitive_prelude_import_map(module_id);
        let staged = Program {
            items: parsed.items.clone(),
            module_interfaces: Default::default(),
            external_module_interfaces: Default::default(),
            module_docs: Default::default(),
            module_type_envs: Default::default(),
            opaque_inners: Default::default(),
            brand_inners: Default::default(),
            structs: Default::default(),
            struct_field_types: Default::default(),
        };
        let mut program = self.resolve_program_from_demands(t, None, staged, BTreeMap::new(), tel)?;
        program
            .module_type_envs
            .entry(String::new())
            .or_default()
            .extend_env(root_types.env);
        program.opaque_inners.extend(root_types.opaque_inners);
        program.brand_inners.extend(root_types.brand_inners);

        let prepared = PreparedPrelude { program, imports };
        let module = self.module(module_id).clone();
        tel.execute(
            &["fz", "compiler", "prelude_prepared"],
            &measurements! {
                items: prepared.program.items.len() as u64,
                imports: prepared.imports.len() as u64,
                root_attrs: parsed.attrs.len() as u64,
            },
            &metadata! {
                module_key: module.key_render(),
                module_key_kind: module.key_kind(),
                module_origin: self.module_origin_kind(module_id),
                source_name: self.file(self.declared_module_file_id(module_id)).descriptor.source_name.clone(),
            },
        );
        self.modules[module_id.0 as usize].prepared_prelude = Some(prepared.clone());
        Ok(prepared)
    }

    pub(crate) fn ensure_body_surface(
        &mut self,
        module_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<ModuleBodySurface, Diagnostic> {
        self.ensure_module_readiness_result(module_id, ModuleReadinessFact::BodySurfaceReady, tel, |this| {
            let parsed = this.ensure_parsed(module_id, tel)?;
            let record = this.module(module_id).clone();
            let surface = collect_body_surface(this, module_id, &parsed, tel);
            let measurements = this.state_measurements(module_id);
            for group in &surface.groups {
                this.reserve_named_function_entity(
                    group.source.module_id,
                    group.source.clone(),
                    group.qualified_name(),
                );
                let specs = group
                    .fn_def()
                    .attrs
                    .iter()
                    .filter_map(|attr| match attr {
                        Attribute::Spec(spec) => Some(spec.clone()),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                if !specs.is_empty() {
                    this.record_function_source_specs(&group.source, &specs);
                }
                if !group.is_private {
                    let local_name = group.fn_def().name.clone();
                    this.record_visible_callable(
                        group.source.module_id,
                        local_name,
                        group.source.arity,
                        group.source.clone(),
                        VisibleCallableAliasOrigin::SourceDeclaration,
                    );
                }
                tel.execute(
                    &["fz", "compiler", "fn_group_discovered"],
                    &measurements! {
                        module_id: module_id.0,
                        file_id: this.declared_module_file_id(module_id).0,
                        fn_group_id: group.id.0,
                        arity: group.source.arity as u64,
                    },
                    &metadata! {
                        module_key: record.key_render(),
                        module_key_kind: record.key_kind(),
                        module_origin: this.module_origin_kind(module_id),
                        owner_module: this.module_display_name(group.source.module_id),
                        fn_name: group.qualified_name(),
                        visibility: if group.is_private { "private" } else { "public" },
                    },
                );
            }
            tel.execute(
                &["fz", "compiler", "body_surface_ready"],
                &measurements,
                &metadata! {
                    module_key: record.key_render(),
                    module_key_kind: record.key_kind(),
                    module_origin: this.module_origin_kind(module_id),
                    owner_module: surface.owner_module.clone(),
                    groups: surface.groups.len() as u64,
                    parse_kind: parsed.parse_kind().as_str(),
                },
            );
            this.modules[module_id.0 as usize].body_surface = Some(surface);
            Ok(())
        })?;

        Ok(self.modules[module_id.0 as usize]
            .body_surface
            .clone()
            .expect("body_surface_ready invariant violated"))
    }

    pub(crate) fn ensure_interface_table(
        &mut self,
        module_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<BTreeMap<ModuleName, ModuleInterface>, Diagnostic> {
        self.ensure_module_readiness_result(module_id, ModuleReadinessFact::InterfaceTableReady, tel, |this| {
            let _ = this.ensure_body_surface(module_id, tel)?;
            let parsed = this.ensure_parsed(module_id, tel)?;
            let interfaces = collect_interfaces(&parsed);
            this.record_module_interface_contracts(module_id, &interfaces);
            let measurements = this.state_measurements(module_id);
            tel.execute(
                &["fz", "compiler", "interface_ready"],
                &measurements,
                &metadata! {
                    module_key: this.module(module_id).key_render(),
                    module_key_kind: this.module(module_id).key_kind(),
                    module_origin: this.module_origin_kind(module_id),
                    interfaces: interfaces.len() as u64,
                    parse_kind: parsed.parse_kind().as_str(),
                },
            );
            this.modules[module_id.0 as usize].interfaces = Some(interfaces);
            Ok(())
        })?;

        Ok(self.modules[module_id.0 as usize]
            .interfaces
            .clone()
            .expect("interface_ready invariant violated"))
    }

    pub(crate) fn ensure_runtime_module_interface(
        &mut self,
        module: &ModuleName,
        tel: &dyn Telemetry,
    ) -> Result<Option<ModuleInterface>, Diagnostic> {
        let Some(module_id) = self.discover_runtime_module(module, tel) else {
            return Ok(None);
        };
        let interfaces = self.ensure_interface_table(module_id, tel)?;
        Ok(interfaces.get(module).cloned())
    }

    pub(crate) fn attach_primitive_prelude_namespace(
        &mut self,
        module_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<(), Diagnostic> {
        let prelude_id = self.discover_primitive_prelude(tel);
        self.ensure_primitive_prelude_namespace(prelude_id, tel)?;
        self.set_namespace_parent(module_id, prelude_id);
        Ok(())
    }

    pub(crate) fn note_namespace_ready(&mut self, module_id: ModuleId, tel: &dyn Telemetry) -> bool {
        self.ensure_module_readiness(module_id, ModuleReadinessFact::NamespaceReady, tel, |this| {
            this.emit_namespace_ready(module_id, tel);
        })
    }

    fn emit_namespace_ready(&self, module_id: ModuleId, tel: &dyn Telemetry) {
        let measurements = self.state_measurements(module_id);
        let namespace = self.namespace(self.module(module_id).namespace_id);
        let record = self.module(module_id);
        tel.execute(
            &["fz", "compiler", "namespace_ready"],
            &measurements,
            &metadata! {
                module_key: record.key_render(),
                module_key_kind: record.key_kind(),
                module_origin: self.module_origin_kind(module_id),
                callables: namespace.callable_bindings.len() as u64,
                modules: namespace.module_bindings.len() as u64,
            },
        );
    }

    pub(crate) fn record_supplemental_module_contracts(
        &mut self,
        interfaces: &BTreeMap<ModuleName, ModuleInterface>,
        tel: &dyn Telemetry,
    ) {
        for (module, interface) in interfaces {
            let module_id = self.reference_named_module(module.clone(), tel);
            if self.module_origin(module_id).is_none() {
                let _ = self.declare_module(
                    Some(ModuleKey::Named(module.clone())),
                    ModuleOrigin::Supplemental,
                    FileOrigin::Supplemental(format!("supplemental:{}", module.dotted())),
                    SourceDescriptor {
                        source_name: format!("supplemental:{}", module.dotted()),
                        text: Arc::<str>::from(""),
                        parse_kind: ParseKind::Program,
                    },
                    tel,
                );
            }
            let origin = if self.module_origin(module_id) == Some(ModuleOrigin::Supplemental) {
                ModuleContractOrigin::Supplemental
            } else {
                ModuleContractOrigin::CompilerOwned(self.declared_module_origin(module_id))
            };
            self.record_module_contract(module_id, interface.clone(), origin);
        }
    }

    pub(crate) fn discover_runtime_export_owner(
        &mut self,
        target: &ExportKey,
        tel: &dyn Telemetry,
    ) -> Result<Option<ModuleId>, Diagnostic> {
        if let Some(existing) = self.module_id_for_name(&target.module)
            && self.module_origin(existing) != Some(ModuleOrigin::EmbeddedRuntime)
        {
            return Ok(None);
        }
        if let Some(owner_module) = self.protocol_callback_owners.get(target).cloned() {
            if let Some(existing) = self.module_id_for_name(&owner_module)
                && self.module_origin(existing) != Some(ModuleOrigin::EmbeddedRuntime)
            {
                return Ok(None);
            }
            return Ok(self.discover_runtime_module(&owner_module, tel));
        }
        if let Some(existing) = self.module_id_for_name(&target.module) {
            if self.module_origin(existing) == Some(ModuleOrigin::EmbeddedRuntime) {
                return Ok(Some(existing));
            }
            return Ok(None);
        }
        if let Some(module_id) = self.discover_runtime_module(&target.module, tel) {
            return Ok(Some(module_id));
        }
        for source in RUNTIME_MODULE_SOURCES {
            let module = ModuleName::from_segments(vec![source.name.to_string()]);
            if let Some(existing) = self.module_id_for_name(&module)
                && self.module_origin(existing) != Some(ModuleOrigin::EmbeddedRuntime)
            {
                continue;
            }
            let Some(candidate) = self.ensure_runtime_module_interface(&module, tel)? else {
                continue;
            };
            if candidate
                .protocol_impls
                .iter()
                .flat_map(|protocol_impl| protocol_impl.callbacks.iter())
                .any(|callback| callback == target)
            {
                return Ok(self.module_id_for_name(&module));
            }
        }
        Ok(None)
    }

    pub(crate) fn source_fn_group_descriptor(
        &mut self,
        module_id: ModuleId,
        name: &str,
        arity: usize,
        tel: &dyn Telemetry,
    ) -> Result<Option<FnGroupDescriptor>, Diagnostic> {
        let surface = self.ensure_body_surface(module_id, tel)?;
        let key = self.source_fn_key_for_qualified_name(module_id, name, arity)?;
        Ok(surface.groups.into_iter().find(|group| group.source == key))
    }

    pub(crate) fn source_fn_group_descriptor_for_key(
        &mut self,
        module_id: ModuleId,
        key: &SourceFnKey,
        tel: &dyn Telemetry,
    ) -> Result<Option<FnGroupDescriptor>, Diagnostic> {
        let surface = self.ensure_body_surface(module_id, tel)?;
        Ok(surface.groups.into_iter().find(|group| &group.source == key))
    }

    pub(crate) fn lowered_group(&self, module_id: ModuleId, source_key: &SourceFnKey) -> Option<LoweredFnGroup> {
        self.modules[module_id.0 as usize]
            .lowered_groups
            .get(source_key)
            .cloned()
    }

    pub(crate) fn runtime_entry_fn_keys(&self, module_id: ModuleId) -> HashSet<Mfa> {
        self.modules[module_id.0 as usize].runtime_entry_fns.clone()
    }

    pub(crate) fn runtime_source_fn_key_for_export_target(
        &mut self,
        owner_module_id: ModuleId,
        target: &ExportKey,
        tel: &dyn Telemetry,
    ) -> Result<Mfa, Diagnostic> {
        let _ = self.ensure_body_surface(owner_module_id, tel)?;
        let qualified_name = format!("{}.{}", target.module, target.name);
        self.source_fn_key_for_qualified_name(owner_module_id, &qualified_name, target.arity)
    }

    pub(crate) fn record_lowered_group(&mut self, module_id: ModuleId, group: LoweredFnGroup) {
        self.modules[module_id.0 as usize]
            .lowered_groups
            .insert(group.source.clone(), group);
    }

    pub(crate) fn ensure_source_module_interfaces(
        &mut self,
        root_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<BTreeMap<ModuleName, ModuleInterface>, Diagnostic> {
        let interfaces = self.ensure_interface_table(root_id, tel)?;
        let named_module_origin = named_module_origin_for_source_owner(self.declared_module_origin(root_id));
        let file_id = self.declared_module_file_id(root_id);
        let file = self.file(file_id).clone();
        for (module, interface) in &interfaces {
            let module_id = self.declare_module(
                Some(ModuleKey::Named(module.clone())),
                named_module_origin,
                file.origin.clone(),
                file.descriptor.clone(),
                tel,
            );
            let _ = self.ensure_body_surface(module_id, tel)?;
            let interface = interface.clone();
            let module = module.clone();
            let mut single = BTreeMap::new();
            single.insert(module, interface);
            let _ = self.ensure_module_readiness(module_id, ModuleReadinessFact::InterfaceTableReady, tel, |this| {
                this.record_module_interface_contracts(module_id, &single);
                let measurements = this.state_measurements(module_id);
                let record = this.module(module_id);
                tel.execute(
                    &["fz", "compiler", "interface_ready"],
                    &measurements,
                    &metadata! {
                        module_key: record.key_render(),
                        module_key_kind: record.key_kind(),
                        module_origin: this.module_origin_kind(module_id),
                        interfaces: 1_u64,
                        parse_kind: file.descriptor.parse_kind.as_str(),
                    },
                );
                this.modules[module_id.0 as usize].interfaces = Some(single);
            });
        }
        Ok(interfaces)
    }

    pub(crate) fn ensure_source_module_macro_exports(
        &mut self,
        root_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<SourceMacroExports, Diagnostic> {
        let parsed = self.ensure_program(root_id, tel)?;
        let exports = collect_source_macro_exports(&parsed.program);
        self.modules[root_id.0 as usize].macro_exports = Some(exports.root.clone());

        let named_module_origin = named_module_origin_for_source_owner(self.declared_module_origin(root_id));
        let file_id = self.declared_module_file_id(root_id);
        let file = self.file(file_id).clone();
        for (module, macros) in &exports.modules {
            let module_id = self.declare_module(
                Some(ModuleKey::Named(module.clone())),
                named_module_origin,
                file.origin.clone(),
                file.descriptor.clone(),
                tel,
            );
            self.modules[module_id.0 as usize].macro_exports = Some(macros.clone());
        }

        Ok(exports)
    }

    pub(crate) fn discover_runtime_reachable_modules(
        &mut self,
        root_interfaces: &BTreeMap<ModuleName, ModuleInterface>,
        seeds: impl IntoIterator<Item = RuntimeReachabilitySeed>,
        tel: &dyn Telemetry,
    ) -> Result<Vec<ModuleId>, Diagnostic> {
        let mut queue = VecDeque::new();
        let mut reachable = Vec::new();

        for interface in root_interfaces.values() {
            enqueue_runtime_interface_imports(self, tel, &mut queue, interface, "program_import");
            enqueue_runtime_protocol_impl_protocols(self, tel, &mut queue, interface, "program_protocol_impl");
        }
        queue.extend(seeds);

        while let Some(candidate) = queue.pop_front() {
            if self.module_origin(candidate.module_id) != Some(ModuleOrigin::EmbeddedRuntime) {
                continue;
            }
            let mut needs_materialization = false;
            if let Some(entry) = candidate.entry.clone() {
                let inserted = self.modules[candidate.module_id.0 as usize]
                    .runtime_entry_fns
                    .insert(entry.clone());
                if inserted {
                    needs_materialization = true;
                    let record = self.module(candidate.module_id);
                    tel.execute(
                        &["fz", "compiler", "runtime_entry_requested"],
                        &self.state_measurements(candidate.module_id),
                        &metadata! {
                            module_key: record.key_render(),
                            module_key_kind: record.key_kind(),
                            module_origin: self.module_origin_kind(candidate.module_id),
                            fn_name: self.render_mfa(&entry),
                            reason: candidate.reason,
                            from_module: candidate
                                .from_module
                                .as_ref()
                                .map(ModuleName::dotted)
                                .unwrap_or_default(),
                        },
                    );
                }
            }
            let newly_reachable = self.mark_reachable(candidate.module_id, ReachabilityKind::Runtime, tel);
            if !newly_reachable && !needs_materialization {
                continue;
            }

            reachable.push(candidate.module_id);
            if !newly_reachable {
                continue;
            }

            let record = self.module(candidate.module_id);
            tel.execute(
                &["fz", "compiler", "runtime_module_reachable"],
                &self.state_measurements(candidate.module_id),
                &metadata! {
                    module_key: record.key_render(),
                    module_key_kind: record.key_kind(),
                    module_origin: self.module_origin_kind(candidate.module_id),
                    reason: candidate.reason,
                    from_module: candidate
                        .from_module
                        .as_ref()
                        .map(ModuleName::dotted)
                        .unwrap_or_default(),
                },
            );

            let Some(ModuleKey::Named(module_name)) = record.key.clone() else {
                continue;
            };
            let interface = self
                .ensure_runtime_module_interface(&module_name, tel)?
                .expect("discovered runtime module must have interface");
            enqueue_runtime_interface_imports(self, tel, &mut queue, &interface, "runtime_import");
            enqueue_runtime_protocol_impl_protocols(
                self,
                tel,
                &mut queue,
                &interface,
                "runtime_protocol_impl_protocol",
            );
            for module in runtime_library::implementation_dependencies(self, &module_name, tel)? {
                let Some(module_id) = self.discover_runtime_module(&module, tel) else {
                    continue;
                };
                queue.push_back(RuntimeReachabilitySeed::new(
                    module_id,
                    "runtime_implementation_dependency",
                    Some(module_name.clone()),
                ));
            }
            enqueue_runtime_protocol_impl_providers(self, tel, &mut queue, &interface)?;
        }

        Ok(reachable)
    }

    fn finish_runtime_module_compilation(
        &mut self,
        module_id: ModuleId,
        lowered_functions: usize,
        planned_specs: usize,
        tel: &dyn Telemetry,
    ) {
        let lowered_advanced =
            self.ensure_module_readiness(module_id, ModuleReadinessFact::RuntimeLowered, tel, |_| {});
        let planned_advanced =
            self.ensure_module_readiness(module_id, ModuleReadinessFact::RuntimePlanned, tel, |_| {});

        let record = &mut self.modules[module_id.0 as usize];
        record.runtime_materialized_entry_fns = record.runtime_entry_fns.clone();
        record.runtime_lowered_functions = Some(lowered_functions);
        record.runtime_planned_specs = Some(planned_specs);

        if lowered_advanced {
            let record = self.module(module_id);
            let groups = record.lowered_groups.len() as u64;
            tel.execute(
                &["fz", "compiler", "runtime_lowered"],
                &measurements! {
                    module_id: module_id.0,
                    file_id: self.declared_module_file_id(module_id).0,
                    functions: lowered_functions as u64,
                    groups: groups,
                    units: groups,
                },
                &metadata! {
                    module_key: record.key_render(),
                    module_key_kind: record.key_kind(),
                    module_origin: self.module_origin_kind(module_id),
                },
            );
        }
        if planned_advanced {
            let record = self.module(module_id);
            let groups = record.lowered_groups.len() as u64;
            tel.execute(
                &["fz", "compiler", "runtime_planned"],
                &measurements! {
                    module_id: module_id.0,
                    file_id: self.declared_module_file_id(module_id).0,
                    planned_specs: planned_specs as u64,
                    groups: groups,
                    units: groups,
                },
                &metadata! {
                    module_key: record.key_render(),
                    module_key_kind: record.key_kind(),
                    module_origin: self.module_origin_kind(module_id),
                },
            );
        }
    }

    pub(crate) fn record_macro_surface(
        &mut self,
        module_id: ModuleId,
        surface: ModuleMacroSurface,
        tel: &dyn Telemetry,
    ) -> bool {
        let _ = self
            .ensure_interface_table(module_id, tel)
            .expect("macro surface requires source-backed interface readiness");
        self.ensure_module_readiness(module_id, ModuleReadinessFact::MacroSurfaceReady, tel, |this| {
            let measurements = this.state_measurements(module_id);
            let record = this.module(module_id);
            tel.execute(
                &["fz", "compiler", "macro_surface_ready"],
                &measurements,
                &metadata! {
                    module_key: record.key_render(),
                    module_key_kind: record.key_kind(),
                    module_origin: this.module_origin_kind(module_id),
                    macros: surface.exports.len() as u64,
                    items: surface.program.items.len() as u64,
                },
            );
            let slot = &mut this.modules[module_id.0 as usize];
            slot.macro_exports = Some(surface.exports.clone());
            slot.macro_surface = Some(surface);
        })
    }

    pub(crate) fn macro_scope_for_root(&self, root_id: ModuleId) -> Option<Program> {
        let file_id = self.declared_module_file_id(root_id);
        let mut items = Vec::new();
        let mut seen_fns = HashSet::new();
        let mut module_docs = HashMap::new();

        for module in &self.modules {
            if module.file_id() != Some(file_id) {
                continue;
            }
            let Some(surface) = &module.macro_surface else {
                continue;
            };
            for item in &surface.program.items {
                let Item::Fn(def) = &**item else {
                    continue;
                };
                if seen_fns.insert(def.name.clone()) {
                    items.push(item.clone());
                }
            }
            for (path, doc) in &surface.program.module_docs {
                module_docs.entry(path.clone()).or_insert_with(|| doc.clone());
            }
        }

        if items.is_empty() {
            return None;
        }

        Some(Program {
            items,
            module_docs,
            ..Program::default()
        })
    }

    pub(crate) fn mark_reachable(&mut self, module_id: ModuleId, kind: ReachabilityKind, tel: &dyn Telemetry) -> bool {
        let record = self.module(module_id);
        if record.reachability.is_marked(kind) {
            tel.execute(
                &["fz", "compiler", "cache_hit"],
                &self.state_measurements(module_id),
                &metadata! {
                    module_key: record.key_render(),
                    module_key_kind: record.key_kind(),
                    phase: "reachability",
                    reachability: kind.as_str(),
                },
            );
            return false;
        }

        let measurements = self.state_measurements(module_id);
        let record = &mut self.modules[module_id.0 as usize];
        record.reachability.mark(kind);
        tel.execute(
            &["fz", "compiler", "module_reachable"],
            &measurements,
            &metadata! {
                module_key: record.key_render(),
                module_key_kind: record.key_kind(),
                module_origin: self.module_origin_kind(module_id),
                reachability: kind.as_str(),
            },
        );
        true
    }

    pub(crate) fn validate_invariants(&self) -> Result<(), CompilerInvariantError> {
        for (idx, file) in self.files.iter().enumerate() {
            let expected = FileId(idx as u32);
            if file.id != expected {
                return Err(CompilerInvariantError::new(format!(
                    "file table invariant violated at index {idx}: stored {:?}, expected {:?}",
                    file.id, expected
                )));
            }
            match self.file_index.get(&file.origin) {
                Some(found) if *found == file.id => {}
                Some(found) => {
                    return Err(CompilerInvariantError::new(format!(
                        "file index invariant violated for `{}`: stored {:?}, indexed {:?}",
                        file.origin.render(),
                        file.id,
                        found
                    )));
                }
                None => {
                    return Err(CompilerInvariantError::new(format!(
                        "file index missing entry for `{}`",
                        file.origin.render()
                    )));
                }
            }
            if file.source.is_some()
                && file.descriptor.text.is_empty()
                && !matches!(file.origin, FileOrigin::Supplemental(_) | FileOrigin::Synthetic(_))
            {
                return Err(CompilerInvariantError::new(format!(
                    "file `{}` loaded empty source unexpectedly",
                    file.origin.render()
                )));
            }
        }

        for (idx, function) in self.functions.iter().enumerate() {
            let expected = FnId(idx as u32);
            if function.id != expected {
                return Err(CompilerInvariantError::new(format!(
                    "function table invariant violated at index {idx}: stored {:?}, expected {:?}",
                    function.id, expected
                )));
            }
            if function.owner_module_id.0 as usize >= self.modules.len() {
                return Err(CompilerInvariantError::new(format!(
                    "function {:?} references missing owner module {:?}",
                    function.id, function.owner_module_id
                )));
            }
            if let FunctionKey::Named(mfa) = &function.key {
                if mfa.module_id != function.owner_module_id {
                    return Err(CompilerInvariantError::new(format!(
                        "named function {:?} owner {:?} does not match MFA owner {:?}",
                        function.id, function.owner_module_id, mfa.module_id
                    )));
                }
                match self.named_function_ids.get(mfa) {
                    Some(found) if *found == function.id => {}
                    Some(found) => {
                        return Err(CompilerInvariantError::new(format!(
                            "named function `{}` maps to {:?} instead of {:?}",
                            self.render_mfa(mfa),
                            found,
                            function.id
                        )));
                    }
                    None => {
                        return Err(CompilerInvariantError::new(format!(
                            "named function `{}` missing index entry",
                            self.render_mfa(mfa)
                        )));
                    }
                }
                match self.named_function_keys.get(&function.id) {
                    Some(found) if found == mfa => {}
                    Some(found) => {
                        return Err(CompilerInvariantError::new(format!(
                            "named function id {:?} reverses to `{}` instead of `{}`",
                            function.id,
                            self.render_mfa(found),
                            self.render_mfa(mfa)
                        )));
                    }
                    None => {
                        return Err(CompilerInvariantError::new(format!(
                            "named function id {:?} missing reverse MFA entry",
                            function.id
                        )));
                    }
                }
            }
        }

        for (idx, module) in self.modules.iter().enumerate() {
            let expected = ModuleId(idx as u32);
            if module.id != expected {
                return Err(CompilerInvariantError::new(format!(
                    "module table invariant violated at index {idx}: stored {:?}, expected {:?}",
                    module.id, expected
                )));
            }
            if let Some(file_id) = module.file_id() {
                if file_id.0 as usize >= self.files.len() {
                    return Err(CompilerInvariantError::new(format!(
                        "module `{}` references missing file {:?}",
                        module.key_render(),
                        file_id
                    )));
                }
            }
            if let Some(key) = &module.key {
                match self.module_index.get(key) {
                    Some(found) if *found == module.id => {}
                    Some(found) => {
                        return Err(CompilerInvariantError::new(format!(
                            "module index invariant violated for `{}`: stored {:?}, indexed {:?}",
                            module.key_render(),
                            module.id,
                            found
                        )));
                    }
                    None => {
                        return Err(CompilerInvariantError::new(format!(
                            "module index missing entry for `{}`",
                            module.key_render()
                        )));
                    }
                }
            }

            if module.declaration.is_none()
                && (module.readiness.source_ready
                    || module.readiness.parsed
                    || module.readiness.namespace_ready
                    || module.readiness.body_surface_ready
                    || module.readiness.interface_table_ready
                    || module.readiness.macro_surface_ready
                    || module.readiness.runtime_lowered
                    || module.readiness.runtime_planned)
            {
                return Err(CompilerInvariantError::new(format!(
                    "undeclared module `{}` recorded readiness facts",
                    module.key_render()
                )));
            }

            let Some(file_id) = module.file_id() else {
                continue;
            };

            let file = self.file(file_id);
            if module.readiness.has(ModuleReadinessFact::SourceReady) && file.source.is_none() {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` is source_ready without source text",
                    module.key_render()
                )));
            }
            if module.readiness.has(ModuleReadinessFact::Parsed) && file.parsed.is_none() {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` is parsed without parsed source",
                    module.key_render()
                )));
            }
            if module.readiness.has(ModuleReadinessFact::BodySurfaceReady) && module.body_surface.is_none() {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` is body_surface_ready without body surface",
                    module.key_render()
                )));
            }
            if module.readiness.has(ModuleReadinessFact::InterfaceTableReady) && module.interfaces.is_none() {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` is interface_ready without interface table",
                    module.key_render()
                )));
            }
            if matches!(module.key, Some(ModuleKey::Named(_)))
                && module.readiness.has(ModuleReadinessFact::InterfaceTableReady)
                && module.origin() != Some(ModuleOrigin::PrimitivePrelude)
                && module.contract.is_none()
                && module
                    .interfaces
                    .as_ref()
                    .and_then(|interfaces| match &module.key {
                        Some(ModuleKey::Named(module_name)) => Some(interfaces.contains_key(module_name)),
                        _ => None,
                    })
                    .unwrap_or(false)
            {
                return Err(CompilerInvariantError::new(format!(
                    "named module `{}` is interface_ready without declared contract",
                    module.key_render()
                )));
            }
            if let Some(surface) = &module.body_surface {
                if surface.owner_module_id != module.id {
                    return Err(CompilerInvariantError::new(format!(
                        "module `{}` body surface owner id {:?} does not match module id {:?}",
                        module.key_render(),
                        surface.owner_module_id,
                        module.id
                    )));
                }
                let expected_owner = self.module_display_name(module.id);
                if surface.owner_module != expected_owner {
                    return Err(CompilerInvariantError::new(format!(
                        "module `{}` body surface owner `{}` does not match module owner `{}`",
                        module.key_render(),
                        surface.owner_module,
                        expected_owner
                    )));
                }
                if surface.groups.len() != surface.group_by_source.len() {
                    return Err(CompilerInvariantError::new(format!(
                        "module `{}` body surface has {} groups but {} source mappings",
                        module.key_render(),
                        surface.groups.len(),
                        surface.group_by_source.len()
                    )));
                }
                for (index, group) in surface.groups.iter().enumerate() {
                    let expected_group_id = FnGroupId(index as u32);
                    if group.id != expected_group_id {
                        return Err(CompilerInvariantError::new(format!(
                            "module `{}` body group `{}` stored id {:?}, expected {:?}",
                            module.key_render(),
                            group.qualified_name(),
                            group.id,
                            expected_group_id
                        )));
                    }
                    match surface.group_by_source.get(&group.source) {
                        Some(found) if *found == group.id => {}
                        Some(found) => {
                            return Err(CompilerInvariantError::new(format!(
                                "module `{}` body group `{}` source key maps to {:?} instead of {:?}",
                                module.key_render(),
                                group.qualified_name(),
                                found,
                                group.id
                            )));
                        }
                        None => {
                            return Err(CompilerInvariantError::new(format!(
                                "module `{}` body group `{}` missing source key mapping",
                                module.key_render(),
                                group.qualified_name()
                            )));
                        }
                    }
                    if !body_surface_group_belongs_to_surface(self, surface.owner_module_id, group.source.module_id) {
                        return Err(CompilerInvariantError::new(format!(
                            "module `{}` body group `{}` owner `{}` does not match surface owner `{}`",
                            module.key_render(),
                            group.qualified_name(),
                            self.module_display_name(group.source.module_id),
                            surface.owner_module
                        )));
                    }
                }
                for source_key in module.lowered_groups.keys() {
                    if !surface.groups.iter().any(|group| &group.source == source_key) {
                        return Err(CompilerInvariantError::new(format!(
                            "module `{}` lowered group `{}` has no body-surface descriptor",
                            module.key_render(),
                            self.render_mfa(source_key)
                        )));
                    }
                }
                let mut seen_function_ids = HashSet::new();
                for lowered in module.lowered_groups.values() {
                    if lowered.fns.len() != lowered.function_ids.len() {
                        return Err(CompilerInvariantError::new(format!(
                            "module `{}` lowered group {:?} has {} fns but {} function ids",
                            module.key_render(),
                            lowered.id,
                            lowered.fns.len(),
                            lowered.function_ids.len()
                        )));
                    }
                    let descriptor = surface
                        .groups
                        .iter()
                        .find(|group| group.source == lowered.source)
                        .expect("lowered-group descriptor presence already checked");
                    if lowered.source != descriptor.source {
                        return Err(CompilerInvariantError::new(format!(
                            "module `{}` lowered group {:?} source `{}` does not match descriptor `{}`",
                            module.key_render(),
                            lowered.id,
                            self.render_mfa(&lowered.source),
                            descriptor.qualified_name()
                        )));
                    }
                    if !lowered
                        .fns
                        .iter()
                        .any(|fn_ir| fn_ir.name == descriptor.qualified_name())
                    {
                        return Err(CompilerInvariantError::new(format!(
                            "module `{}` lowered group {:?} does not contain root fn `{}`",
                            module.key_render(),
                            lowered.id,
                            descriptor.qualified_name()
                        )));
                    }
                    for (fn_ir, function_id) in lowered.fns.iter().zip(&lowered.function_ids) {
                        if fn_ir.id != *function_id {
                            return Err(CompilerInvariantError::new(format!(
                                "module `{}` lowered group {:?} stored fn {:?} but function_ids recorded {:?}",
                                module.key_render(),
                                lowered.id,
                                fn_ir.id,
                                function_id
                            )));
                        }
                        if !seen_function_ids.insert(*function_id) {
                            return Err(CompilerInvariantError::new(format!(
                                "module `{}` lowered fn {:?} belongs to more than one cached group",
                                module.key_render(),
                                function_id
                            )));
                        }
                    }
                }
            }
            if module.readiness.has(ModuleReadinessFact::MacroSurfaceReady) && module.macro_surface.is_none() {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` is macro_surface_ready without macro surface",
                    module.key_render()
                )));
            }
            if module.readiness.has(ModuleReadinessFact::MacroSurfaceReady)
                && !module.readiness.has(ModuleReadinessFact::InterfaceTableReady)
            {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` reached macro surface without interface readiness",
                    module.key_render()
                )));
            }
            if let Some(surface) = &module.macro_surface {
                if surface.program.items.iter().any(|item| !matches!(&**item, Item::Fn(_))) {
                    return Err(CompilerInvariantError::new(format!(
                        "module `{}` macro surface contains non-function items",
                        module.key_render()
                    )));
                }
            }
            if module.prepared_prelude.is_some() && module.origin() != Some(ModuleOrigin::PrimitivePrelude) {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` cached prepared prelude but is not the primitive prelude",
                    module.key_render()
                )));
            }
            if module.readiness.has(ModuleReadinessFact::RuntimeLowered) && !module.reachability.runtime {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` reached runtime_lowered without runtime reachability",
                    module.key_render()
                )));
            }
            if module.readiness.has(ModuleReadinessFact::RuntimeLowered) && module.runtime_lowered_functions.is_none() {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` reached runtime_lowered without recorded lowered function facts",
                    module.key_render()
                )));
            }
            if module.readiness.has(ModuleReadinessFact::RuntimePlanned)
                && !module.readiness.has(ModuleReadinessFact::RuntimeLowered)
            {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` reached runtime_planned without runtime_lowered",
                    module.key_render()
                )));
            }
            if module.readiness.has(ModuleReadinessFact::RuntimePlanned) && module.runtime_planned_specs.is_none() {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` reached runtime_planned without recorded planned spec facts",
                    module.key_render()
                )));
            }
            if module.origin() == Some(ModuleOrigin::EmbeddedRuntime) && !module.reachability.runtime {
                if !module.lowered_groups.is_empty() {
                    return Err(CompilerInvariantError::new(format!(
                        "runtime module `{}` cached lowered groups without runtime reachability",
                        module.key_render()
                    )));
                }
                if module.readiness.has(ModuleReadinessFact::RuntimeLowered)
                    || module.readiness.has(ModuleReadinessFact::RuntimePlanned)
                {
                    return Err(CompilerInvariantError::new(format!(
                        "runtime module `{}` advanced execution state without runtime reachability",
                        module.key_render()
                    )));
                }
                if module.runtime_lowered_functions.is_some() || module.runtime_planned_specs.is_some() {
                    return Err(CompilerInvariantError::new(format!(
                        "runtime module `{}` recorded readiness facts without runtime reachability",
                        module.key_render()
                    )));
                }
            }
            if module.readiness.has(ModuleReadinessFact::RuntimeLowered) {
                for entry in &module.runtime_materialized_entry_fns {
                    if !module.lowered_groups.contains_key(entry) {
                        return Err(CompilerInvariantError::new(format!(
                            "runtime module `{}` lowered without cached entry group `{}`/{}",
                            module.key_render(),
                            self.render_mfa(entry),
                            entry.arity
                        )));
                    }
                }
            }
        }

        Ok(())
    }

    pub(crate) fn ensure_module_readiness<F>(
        &mut self,
        module_id: ModuleId,
        fact: ModuleReadinessFact,
        tel: &dyn Telemetry,
        work: F,
    ) -> bool
    where
        F: FnOnce(&mut Self),
    {
        self.ensure_module_readiness_result(module_id, fact, tel, |this| {
            work(this);
            Ok::<(), ()>(())
        })
        .expect("infallible compiler readiness work failed unexpectedly")
    }

    pub(crate) fn ensure_module_readiness_result<F, E>(
        &mut self,
        module_id: ModuleId,
        fact: ModuleReadinessFact,
        tel: &dyn Telemetry,
        work: F,
    ) -> Result<bool, E>
    where
        F: FnOnce(&mut Self) -> Result<(), E>,
    {
        let current = self.module(module_id).readiness;
        let metadata = self.readiness_metadata(module_id, current, fact);
        let measurements = self.state_measurements(module_id);
        if current.has(fact) {
            tel.execute(&["fz", "compiler", "cache_hit"], &measurements, &metadata);
            return Ok(false);
        }
        tel.execute(&["fz", "compiler", "cache_miss"], &measurements, &metadata);
        let _span = tel.span(&["fz", "compiler", "readiness_work"], metadata.clone());
        work(self)?;
        self.record_module_readiness(module_id, fact, tel);
        Ok(true)
    }

    fn create_module_record(
        &mut self,
        key: Option<ModuleKey>,
        declaration: Option<ModuleDeclaration>,
        tel: &dyn Telemetry,
    ) -> ModuleId {
        let id = ModuleId(self.modules.len() as u32);
        let namespace_id = NamespaceId(self.namespaces.len() as u32);
        self.namespaces.push(NamespaceRecord {
            id: namespace_id,
            owner_module_id: id,
            parent: None,
            callable_bindings: HashMap::new(),
            module_bindings: HashMap::new(),
        });
        let record = ModuleRecord {
            id,
            key: key.clone(),
            declaration,
            namespace_id,
            readiness: ModuleReadiness::default(),
            reachability: Reachability::default(),
            body_surface: None,
            lowered_groups: HashMap::new(),
            runtime_entry_fns: HashSet::new(),
            runtime_materialized_entry_fns: HashSet::new(),
            runtime_lowered_functions: None,
            runtime_planned_specs: None,
            interfaces: None,
            contract: None,
            macro_exports: None,
            macro_surface: None,
            prepared_prelude: None,
        };
        self.modules.push(record);
        if let Some(key) = key.clone() {
            self.module_index.insert(key, id);
        }
        tel.execute(
            &["fz", "compiler", "module_discovered"],
            &measurements! {
                module_id: id.0,
                file_id: declaration.map_or(u64::MAX as u32, |declaration| declaration.file_id.0),
            },
            &metadata! {
                module_key: self.module(id).key_render(),
                module_key_kind: self.module(id).key_kind(),
                module_origin: self.module_origin_kind(id),
                file_origin: declaration
                    .map(|declaration| self.file(declaration.file_id).origin.kind().to_string())
                    .unwrap_or_else(|| "undeclared".to_string()),
            },
        );
        id
    }

    fn declare_module(
        &mut self,
        key: Option<ModuleKey>,
        origin: ModuleOrigin,
        file_origin: FileOrigin,
        descriptor: SourceDescriptor,
        tel: &dyn Telemetry,
    ) -> ModuleId {
        let module_id = match key.clone() {
            Some(ModuleKey::Named(module)) => self.reference_named_module(module, tel),
            Some(key) => self
                .module_index
                .get(&key)
                .copied()
                .unwrap_or_else(|| self.create_module_record(Some(key), None, tel)),
            None => self.create_module_record(None, None, tel),
        };
        let file_id = self.intern_file(file_origin, descriptor, tel);
        let declaration = ModuleDeclaration { origin, file_id };
        let record = self.module(module_id).clone();
        if let Some(existing) = record.declaration {
            assert_eq!(
                existing.origin,
                origin,
                "compiler module declaration conflict for `{}`: existing origin `{}`, new origin `{}`",
                record.key_render(),
                existing.origin.kind(),
                origin.kind()
            );
            assert_eq!(
                existing.file_id,
                file_id,
                "compiler module declaration conflict for `{}`: existing file {:?}, new file {:?}",
                record.key_render(),
                existing.file_id,
                file_id
            );
            tel.execute(
                &["fz", "compiler", "module_cache_hit"],
                &measurements! { module_id: module_id.0, file_id: file_id.0 },
                &metadata! {
                    module_key: record.key_render(),
                    module_key_kind: record.key_kind(),
                    module_origin: existing.origin.kind(),
                    file_origin: self.file(file_id).origin.kind(),
                },
            );
            return module_id;
        }
        self.modules[module_id.0 as usize].declaration = Some(declaration);
        tel.execute(
            &["fz", "compiler", "module_declared"],
            &measurements! { module_id: module_id.0, file_id: file_id.0 },
            &metadata! {
                module_key: self.module(module_id).key_render(),
                module_key_kind: self.module(module_id).key_kind(),
                module_origin: origin.kind(),
                file_origin: self.file(file_id).origin.kind(),
            },
        );
        module_id
    }

    fn record_module_interface_contracts(
        &mut self,
        module_id: ModuleId,
        interfaces: &BTreeMap<ModuleName, ModuleInterface>,
    ) {
        self.record_protocol_facts_from_interfaces(interfaces);
        let Some(ModuleKey::Named(module_name)) = self.module(module_id).key.clone() else {
            return;
        };
        let Some(interface) = interfaces.get(&module_name) else {
            return;
        };
        self.record_module_contract(
            module_id,
            interface.clone(),
            ModuleContractOrigin::CompilerOwned(self.declared_module_origin(module_id)),
        );
    }

    fn record_protocol_facts_from_interfaces(&mut self, interfaces: &BTreeMap<ModuleName, ModuleInterface>) {
        let mut protocol_decls = BTreeMap::new();
        let mut protocol_impls = BTreeMap::new();
        extend_protocol_facts_from_interfaces(&mut protocol_decls, &mut protocol_impls, interfaces);
        self.record_protocol_facts(&protocol_decls, &protocol_impls);
    }

    pub(crate) fn record_protocol_facts(
        &mut self,
        protocol_decls: &BTreeMap<ModuleName, ProtocolDecl>,
        protocol_impls: &BTreeMap<ProtocolImplKey, ProtocolImplFact>,
    ) {
        for (name, protocol) in protocol_decls {
            match self.protocol_decls.get(name) {
                Some(existing) => {
                    let existing_callbacks = existing
                        .callbacks
                        .iter()
                        .map(|callback| (callback.name.clone(), callback.arity))
                        .collect::<Vec<_>>();
                    let incoming_callbacks = protocol
                        .callbacks
                        .iter()
                        .map(|callback| (callback.name.clone(), callback.arity))
                        .collect::<Vec<_>>();
                    assert_eq!(
                        existing_callbacks, incoming_callbacks,
                        "protocol callback conflict for `{name}`"
                    );
                }
                None => {
                    self.protocol_decls.insert(name.clone(), protocol.clone());
                }
            }
        }

        for (key, implementation) in protocol_impls {
            match self.protocol_impls.get(key) {
                Some(existing) => {
                    assert_eq!(
                        existing.callbacks, implementation.callbacks,
                        "protocol implementation callback conflict for `{}` on `{}`",
                        key.protocol, key.target
                    );
                }
                None => {
                    self.protocol_impls.insert(key.clone(), implementation.clone());
                }
            }

            let ImplTarget::Module(owner_module) = &implementation.target;
            self.protocol_provider_modules
                .entry(implementation.protocol.clone())
                .or_default()
                .insert(owner_module.clone());
            for callback in implementation.callbacks.values() {
                if let Some(existing) = self
                    .protocol_callback_owners
                    .insert(callback.clone(), owner_module.clone())
                {
                    assert_eq!(
                        existing, *owner_module,
                        "protocol callback owner conflict for `{}`: existing `{}`, new `{}`",
                        callback, existing, owner_module
                    );
                }
            }
        }
    }

    pub(crate) fn protocol_decls(&self) -> &BTreeMap<ModuleName, ProtocolDecl> {
        &self.protocol_decls
    }

    pub(crate) fn protocol_impls(&self) -> &BTreeMap<ProtocolImplKey, ProtocolImplFact> {
        &self.protocol_impls
    }

    fn intern_file(&mut self, origin: FileOrigin, descriptor: SourceDescriptor, tel: &dyn Telemetry) -> FileId {
        if let Some(existing) = self.file_index.get(&origin).copied() {
            let existing_record = self.file(existing);
            assert_eq!(
                existing_record.descriptor.source_name,
                descriptor.source_name,
                "compiler file discovery conflict for `{}`: source label changed",
                origin.render()
            );
            assert_eq!(
                existing_record.descriptor.parse_kind,
                descriptor.parse_kind,
                "compiler file discovery conflict for `{}`: parse kind changed",
                origin.render()
            );
            assert_eq!(
                existing_record.descriptor.text,
                descriptor.text,
                "compiler file discovery conflict for `{}`: source text changed",
                origin.render()
            );
            tel.execute(
                &["fz", "compiler", "file_cache_hit"],
                &measurements! { file_id: existing.0 },
                &metadata! {
                    file_origin: origin.kind(),
                    file_label: origin.render(),
                },
            );
            return existing;
        }

        let id = FileId(self.files.len() as u32);
        self.files.push(FileRecord {
            id,
            origin: origin.clone(),
            source: None,
            descriptor,
            parsed: None,
        });
        self.file_index.insert(origin.clone(), id);
        tel.execute(
            &["fz", "compiler", "file_registered"],
            &measurements! { file_id: id.0 },
            &metadata! {
                file_origin: origin.kind(),
                file_label: origin.render(),
            },
        );
        id
    }

    fn record_module_readiness(&mut self, module_id: ModuleId, fact: ModuleReadinessFact, tel: &dyn Telemetry) {
        let measurements = self.state_measurements(module_id);
        let record = &mut self.modules[module_id.0 as usize];
        debug_assert!(
            !record.readiness.has(fact),
            "record_module_readiness called twice for {:?} fact {}",
            module_id,
            fact.as_str()
        );
        record.readiness.record(fact);
        tel.execute(
            &["fz", "compiler", "readiness_recorded"],
            &measurements,
            &metadata! {
                module_key: record.key_render(),
                module_key_kind: record.key_kind(),
                module_origin: self.module_origin_kind(module_id),
                readiness_fact: fact.as_str(),
            },
        );
    }

    fn state_measurements(&self, module_id: ModuleId) -> crate::telemetry::Measurements<'static> {
        let record = self.module(module_id);
        measurements! {
            module_id: module_id.0,
            file_id: record.file_id().map_or(u64::MAX as u32, |file_id| file_id.0),
        }
    }

    fn readiness_metadata(
        &self,
        module_id: ModuleId,
        current: ModuleReadiness,
        fact: ModuleReadinessFact,
    ) -> crate::telemetry::Metadata<'static> {
        let record = self.module(module_id);
        metadata! {
            module_key: record.key_render(),
            module_key_kind: record.key_kind(),
            module_origin: self.module_origin_kind(module_id),
            requested_readiness: fact.as_str(),
            source_ready: current.source_ready,
            parsed_ready: current.parsed,
            namespace_ready: current.namespace_ready,
            body_surface_ready: current.body_surface_ready,
            interface_table_ready: current.interface_table_ready,
            macro_surface_ready: current.macro_surface_ready,
            runtime_lowered_ready: current.runtime_lowered,
            runtime_planned_ready: current.runtime_planned,
        }
    }

    fn module_origin_kind(&self, module_id: ModuleId) -> String {
        self.module_origin(module_id)
            .map(|origin| origin.kind().to_string())
            .unwrap_or_else(|| "undeclared".to_string())
    }
}

fn enqueue_runtime_interface_imports(
    compiler: &mut CompilerWorld,
    tel: &dyn Telemetry,
    queue: &mut VecDeque<RuntimeReachabilitySeed>,
    interface: &ModuleInterface,
    reason: &'static str,
) {
    for import in &interface.imports {
        let Some(module_id) = compiler.discover_runtime_module(&import.module, tel) else {
            continue;
        };
        queue.push_back(RuntimeReachabilitySeed::new(
            module_id,
            reason,
            Some(interface.name.clone()),
        ));
    }
}

fn enqueue_runtime_protocol_impl_protocols(
    compiler: &mut CompilerWorld,
    tel: &dyn Telemetry,
    queue: &mut VecDeque<RuntimeReachabilitySeed>,
    interface: &ModuleInterface,
    reason: &'static str,
) {
    let local_protocols = interface
        .protocols
        .iter()
        .map(|protocol| &protocol.name)
        .collect::<HashSet<_>>();
    for protocol_impl in &interface.protocol_impls {
        if !local_protocols.contains(&protocol_impl.protocol) {
            let Some(module_id) = compiler.discover_runtime_module(&protocol_impl.protocol, tel) else {
                continue;
            };
            queue.push_back(RuntimeReachabilitySeed::new(
                module_id,
                reason,
                Some(interface.name.clone()),
            ));
        }
    }
}

fn enqueue_runtime_protocol_impl_providers(
    compiler: &mut CompilerWorld,
    tel: &dyn Telemetry,
    queue: &mut VecDeque<RuntimeReachabilitySeed>,
    interface: &ModuleInterface,
) -> Result<(), Diagnostic> {
    if interface.protocols.is_empty() {
        return Ok(());
    }
    let protocols = interface
        .protocols
        .iter()
        .map(|protocol| protocol.name.clone())
        .collect::<Vec<_>>();
    for protocol in &protocols {
        let Some(provider_modules) = compiler.protocol_provider_modules.get(protocol).cloned() else {
            continue;
        };
        for module in provider_modules {
            let Some(module_id) = compiler.discover_runtime_module(&module, tel) else {
                continue;
            };
            queue.push_back(RuntimeReachabilitySeed::new(
                module_id,
                "runtime_protocol_impl_provider",
                Some(interface.name.clone()),
            ));
        }
    }
    for source in RUNTIME_MODULE_SOURCES {
        let module = ModuleName::from_segments(vec![source.name.to_string()]);
        if let Some(existing) = compiler.module_id_for_name(&module)
            && compiler.module_origin(existing) != Some(ModuleOrigin::EmbeddedRuntime)
        {
            continue;
        }
        let Some(candidate) = compiler.ensure_runtime_module_interface(&module, tel)? else {
            continue;
        };
        if candidate
            .protocol_impls
            .iter()
            .any(|protocol_impl| protocols.contains(&protocol_impl.protocol))
        {
            let module_id = compiler
                .discover_runtime_module(&module, tel)
                .expect("runtime protocol provider must be discoverable once its interface exists");
            queue.push_back(RuntimeReachabilitySeed::new(
                module_id,
                "runtime_protocol_impl_provider",
                Some(interface.name.clone()),
            ));
        }
    }
    Ok(())
}

fn record_runtime_prelude_namespace(
    compiler: &mut CompilerWorld,
    module_id: ModuleId,
    tel: &dyn Telemetry,
    items: &[Rc<Item>],
) -> Result<(), Diagnostic> {
    for item in items {
        match item.as_ref() {
            Item::Import {
                path,
                only,
                except,
                span,
            } => record_runtime_prelude_import(
                compiler,
                module_id,
                tel,
                path,
                only.as_deref(),
                except.as_deref(),
                *span,
            )?,
            Item::Alias { .. } => {
                panic!("runtime.fz prelude aliases are not supported; use import")
            }
            _ => {}
        }
    }
    Ok(())
}

fn record_runtime_prelude_import(
    compiler: &mut CompilerWorld,
    module_id: ModuleId,
    tel: &dyn Telemetry,
    module: &ModuleName,
    only: Option<&[(String, usize)]>,
    except: Option<&[(String, usize)]>,
    span: Span,
) -> Result<(), Diagnostic> {
    let interface = runtime_library::interface(compiler, module, tel)?.ok_or_else(|| {
        Diagnostic::error(
            crate::diag::codes::RESOLVE_UNKNOWN_MODULE,
            format!("module `{}` is not defined", module),
            span,
        )
    })?;
    let target_module_id = compiler.module_id_for_name(module).ok_or_else(|| {
        Diagnostic::error(
            crate::diag::codes::RESOLVE_UNKNOWN_MODULE,
            format!("module `{}` is not defined", module),
            span,
        )
    })?;
    let mut exports = interface
        .exports
        .iter()
        .map(|export| (export.name.clone(), export.arity))
        .collect::<Vec<_>>();
    if let Some(only) = only {
        for requested in only {
            assert!(
                exports.contains(requested),
                "runtime.fz imports missing `{}/{}` from `{}`",
                requested.0,
                requested.1,
                module
            );
        }
        exports = only.to_vec();
    }
    if let Some(except) = except {
        exports.retain(|export| !except.contains(export));
    }
    for (name, arity) in exports {
        compiler.record_visible_callable_alias(
            module_id,
            name.clone(),
            arity,
            Mfa::new(target_module_id, name, arity),
            VisibleCallableAliasOrigin::PreludeImport {
                from_module: module.clone(),
            },
        );
    }
    Ok(())
}

fn parse_source(
    descriptor: &SourceDescriptor,
    source: &Arc<str>,
    tel: &dyn Telemetry,
) -> Result<ParsedSource, Diagnostic> {
    let mut sm = SourceMap::new();
    let file_id = sm.add_file(descriptor.source_name.clone(), source.clone());
    let toks = Lexer::with_file(source.as_ref(), file_id)
        .tokenize_with_telemetry(tel)
        .map_err(|err| err.to_diagnostic())?;
    let mut parser = Parser::new(toks);
    match descriptor.parse_kind {
        ParseKind::Program => {
            let program = parser
                .parse_program_with_telemetry(tel)
                .map_err(|err| err.to_diagnostic())?;
            Ok(ParsedSource::Program(ParsedProgram { sm, program }))
        }
        ParseKind::Prelude => {
            let (items, attrs) = parser
                .parse_prelude_with_telemetry(tel)
                .map_err(|err| err.to_diagnostic())?;
            Ok(ParsedSource::Prelude(ParsedPrelude { sm, items, attrs }))
        }
    }
}

fn collect_interfaces(parsed: &ParsedSource) -> BTreeMap<ModuleName, ModuleInterface> {
    match parsed {
        ParsedSource::Program(parsed) => collect_from_program(&parsed.program),
        ParsedSource::Prelude(parsed) => {
            let program = Program {
                items: parsed.items.clone(),
                module_interfaces: Default::default(),
                external_module_interfaces: Default::default(),
                module_docs: Default::default(),
                module_type_envs: Default::default(),
                opaque_inners: Default::default(),
                brand_inners: Default::default(),
                structs: Default::default(),
                struct_field_types: Default::default(),
            };
            collect_from_program(&program)
        }
    }
}

fn named_module_origin_for_source_owner(owner_origin: ModuleOrigin) -> ModuleOrigin {
    match owner_origin {
        ModuleOrigin::RootSource | ModuleOrigin::Filesystem => ModuleOrigin::Filesystem,
        ModuleOrigin::Supplemental => ModuleOrigin::Supplemental,
        ModuleOrigin::EmbeddedRuntime => ModuleOrigin::EmbeddedRuntime,
        ModuleOrigin::PrimitivePrelude => ModuleOrigin::PrimitivePrelude,
    }
}

fn collect_body_surface(
    compiler: &mut CompilerWorld,
    surface_module_id: ModuleId,
    parsed: &ParsedSource,
    tel: &dyn Telemetry,
) -> ModuleBodySurface {
    let target_module = match &compiler.module(surface_module_id).key {
        None | Some(ModuleKey::RootPath(_)) => None,
        Some(ModuleKey::Named(_))
            if compiler.module_origin(surface_module_id) == Some(ModuleOrigin::PrimitivePrelude) =>
        {
            None
        }
        Some(ModuleKey::Named(name)) => Some(name.clone()),
    };
    let mut surface = ModuleBodySurface {
        owner_module_id: surface_module_id,
        owner_module: compiler.module_display_name(surface_module_id),
        ..ModuleBodySurface::default()
    };
    let items = match parsed {
        ParsedSource::Program(parsed) => &parsed.program.items,
        ParsedSource::Prelude(parsed) => &parsed.items,
    };
    collect_body_surface_items(
        compiler,
        surface_module_id,
        target_module.as_ref(),
        items,
        None,
        surface_module_id,
        &mut surface,
        tel,
    );
    surface
}

fn collect_body_surface_items(
    compiler: &mut CompilerWorld,
    surface_module_id: ModuleId,
    target_module: Option<&ModuleName>,
    items: &[Rc<Item>],
    current_module: Option<&ModuleName>,
    current_module_id: ModuleId,
    surface: &mut ModuleBodySurface,
    tel: &dyn Telemetry,
) {
    for item in items {
        match &**item {
            Item::Fn(def)
                if def.extern_abi.is_none()
                    && !def.is_macro
                    && body_surface_collects_module(target_module, current_module) =>
            {
                let owner_module = compiler.module_display_name(current_module_id);
                surface.register_source_group(
                    current_module_id,
                    &owner_module,
                    qualify_body_surface_fn_name(&owner_module, &def.name),
                    Rc::new(def.clone()),
                );
            }
            Item::Module(module) => {
                let nested_name = match current_module {
                    Some(parent) => parent.child(module.name.clone()),
                    None => ModuleName::from_segments(vec![module.name.clone()]),
                };
                if !body_surface_should_recurse_into_module(target_module, &nested_name) {
                    continue;
                }
                let nested_module_id =
                    register_named_body_surface_module(compiler, surface_module_id, nested_name.clone(), tel);
                collect_body_surface_items(
                    compiler,
                    surface_module_id,
                    target_module,
                    &module.items,
                    Some(&nested_name),
                    nested_module_id,
                    surface,
                    tel,
                );
            }
            Item::ProtocolImpl(protocol_impl) => {
                collect_protocol_impl_body_surface_groups(
                    compiler,
                    surface_module_id,
                    target_module,
                    protocol_impl,
                    items,
                    current_module,
                    surface,
                    tel,
                );
            }
            _ => {}
        }
    }
}

fn collect_protocol_impl_body_surface_groups(
    compiler: &mut CompilerWorld,
    surface_module_id: ModuleId,
    target_module: Option<&ModuleName>,
    protocol_impl: &ProtocolImplDef,
    siblings: &[Rc<Item>],
    current_module: Option<&ModuleName>,
    surface: &mut ModuleBodySurface,
    tel: &dyn Telemetry,
) {
    let protocol = body_surface_impl_protocol_name(current_module, &protocol_impl.protocol, siblings);
    let target = body_surface_qualify_module_child(current_module, &protocol_impl.target.path);
    let impl_module = body_surface_protocol_impl_module(&protocol, &target);
    if !body_surface_collects_named_module(target_module, &impl_module) {
        return;
    }
    let impl_module_id = register_named_body_surface_module(compiler, surface_module_id, impl_module.clone(), tel);
    let owner_module = compiler.module_display_name(impl_module_id);
    for item in &protocol_impl.items {
        if let Item::Fn(def) = &**item
            && def.extern_abi.is_none()
            && !def.is_macro
        {
            surface.register_source_group(
                impl_module_id,
                &owner_module,
                qualify_body_surface_fn_name(&owner_module, &def.name),
                Rc::new(def.clone()),
            );
        }
    }
}

fn register_named_body_surface_module(
    compiler: &mut CompilerWorld,
    surface_module_id: ModuleId,
    module: ModuleName,
    tel: &dyn Telemetry,
) -> ModuleId {
    let owner = compiler.module(surface_module_id).clone();
    let file = compiler
        .file(compiler.declared_module_file_id(surface_module_id))
        .clone();
    let origin = match compiler.declared_module_origin(surface_module_id) {
        ModuleOrigin::RootSource | ModuleOrigin::Filesystem => ModuleOrigin::Filesystem,
        ModuleOrigin::Supplemental => ModuleOrigin::Supplemental,
        ModuleOrigin::EmbeddedRuntime => ModuleOrigin::EmbeddedRuntime,
        ModuleOrigin::PrimitivePrelude => ModuleOrigin::PrimitivePrelude,
    };
    let _ = owner;
    compiler.declare_module(
        Some(ModuleKey::Named(module)),
        origin,
        file.origin,
        file.descriptor,
        tel,
    )
}

fn body_surface_should_recurse_into_module(target_module: Option<&ModuleName>, candidate: &ModuleName) -> bool {
    match target_module {
        None => true,
        Some(target) => module_name_has_prefix(candidate, target) || module_name_has_prefix(target, candidate),
    }
}

fn body_surface_collects_module(target_module: Option<&ModuleName>, candidate: Option<&ModuleName>) -> bool {
    match (target_module, candidate) {
        (None, _) => true,
        (Some(_), None) => false,
        (Some(target), Some(candidate)) => module_name_has_prefix(candidate, target),
    }
}

fn body_surface_collects_named_module(target_module: Option<&ModuleName>, candidate: &ModuleName) -> bool {
    match target_module {
        None => true,
        Some(target) => module_name_matches_surface(candidate, target),
    }
}

fn module_name_from_dotted(dotted: &str) -> Option<ModuleName> {
    (!dotted.is_empty()).then(|| ModuleName::from_segments(dotted.split('.').map(str::to_string).collect()))
}

fn body_surface_impl_protocol_name(
    parent: Option<&ModuleName>,
    name: &ModuleName,
    siblings: &[Rc<Item>],
) -> ModuleName {
    if name.segments().len() != 1 {
        return name.clone();
    }
    if let Some(parent) = parent {
        let has_local_protocol = siblings.iter().any(|item| {
            matches!(
                &**item,
                Item::Protocol(protocol)
                    if protocol.name.segments().len() == 1
                        && protocol.name.last_segment() == name.last_segment()
            )
        });
        if has_local_protocol || name.last_segment() == parent.last_segment() {
            return if name.last_segment() == parent.last_segment() {
                parent.clone()
            } else {
                parent.child(name.last_segment().to_string())
            };
        }
    }
    name.clone()
}

fn body_surface_qualify_module_child(parent: Option<&ModuleName>, name: &ModuleName) -> ModuleName {
    if name.segments().len() == 1
        && let Some(parent) = parent
    {
        if name.last_segment() == parent.last_segment() {
            parent.clone()
        } else {
            parent.child(name.last_segment().to_string())
        }
    } else {
        name.clone()
    }
}

fn body_surface_protocol_impl_module(protocol: &ModuleName, target: &ModuleName) -> ModuleName {
    protocol.child(target.last_segment().to_string())
}

fn module_name_has_prefix(candidate: &ModuleName, prefix: &ModuleName) -> bool {
    candidate.segments().starts_with(prefix.segments())
}

fn module_name_has_suffix(candidate: &ModuleName, suffix: &ModuleName) -> bool {
    candidate.segments().ends_with(suffix.segments())
}

fn module_name_matches_surface(candidate: &ModuleName, surface: &ModuleName) -> bool {
    module_name_has_prefix(candidate, surface) || module_name_has_suffix(candidate, surface)
}

fn qualify_body_surface_fn_name(owner_module: &str, fn_name: &str) -> String {
    if owner_module.is_empty() {
        fn_name.to_string()
    } else {
        format!("{owner_module}.{fn_name}")
    }
}

fn body_surface_group_belongs_to_surface(
    compiler: &CompilerWorld,
    surface_owner_id: ModuleId,
    group_owner_id: ModuleId,
) -> bool {
    let surface_owner = compiler.module(surface_owner_id);
    let group_owner = compiler.module(group_owner_id);
    match (&surface_owner.key, &group_owner.key) {
        (None | Some(ModuleKey::RootPath(_)), _) => surface_owner.file_id() == group_owner.file_id(),
        (Some(ModuleKey::Named(_)), _) if surface_owner.origin() == Some(ModuleOrigin::PrimitivePrelude) => {
            surface_owner.file_id() == group_owner.file_id()
        }
        (Some(ModuleKey::Named(surface_name)), Some(ModuleKey::Named(group_name))) => {
            group_owner.file_id() == surface_owner.file_id() && module_name_matches_surface(group_name, surface_name)
        }
        (Some(ModuleKey::Named(_)), None | Some(ModuleKey::RootPath(_))) => false,
    }
}

fn collect_source_macro_exports(prog: &Program) -> SourceMacroExports {
    let mut out = SourceMacroExports::default();
    for item in &prog.items {
        match &**item {
            Item::Fn(def) if def.is_macro => {
                let arity = def.clauses.first().map(|clause| clause.params.len()).unwrap_or(0);
                out.root.insert((def.name.clone(), arity));
            }
            Item::Module(module) => collect_module_macro_exports(module, None, &mut out.modules),
            _ => {}
        }
    }
    out
}

fn collect_module_macro_exports(
    module: &ModuleDef,
    parent: Option<&ModuleName>,
    out: &mut HashMap<ModuleName, HashSet<(String, usize)>>,
) {
    let path = if let Some(parent) = parent {
        parent.child(module.name.clone())
    } else {
        ModuleName::from_segments(vec![module.name.clone()])
    };
    let mut macros = HashSet::new();
    for item in &module.items {
        match &**item {
            Item::Fn(def) if def.is_macro => {
                let arity = def.clauses.first().map(|clause| clause.params.len()).unwrap_or(0);
                macros.insert((def.name.clone(), arity));
            }
            Item::Module(inner) => collect_module_macro_exports(inner, Some(&path), out),
            _ => {}
        }
    }
    out.insert(path, macros);
}

#[cfg(test)]
#[path = "compiler_test.rs"]
mod compiler_test;
