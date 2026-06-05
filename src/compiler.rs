#![allow(dead_code)]
// fz-hua.2 makes Compiler the owner of source-backed module state, but the
// later world-model phases are still being pulled into use over the next
// tickets. Keep the allowance local to this module until those phases are live.

use crate::ast::{Attribute, FnDef, Item, ModuleDef, Program, ProtocolImplDef, SpecDecl};
use crate::diag::{Diagnostic, SourceMap, Span};
use crate::frontend::resolve::{
    InterfaceTable, resolve_program_eagerly,
};
use crate::frontend::{
    protocols::{ImplTarget, ProtocolRegistry},
    FrontendErr, FrontendOk, FrontendResult, apply_planned_direct_call_targets, check_frontend_from_entry_fns, macros,
    resolve,
};
use crate::fz_ir::{BlockId, ExternDecl, ExternId, ExternalCallEdge, FnId, FnIr, ProtocolCallTarget, Var};
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
    EmbeddedRuntime,
    PrimitivePrelude,
}

impl ModuleOrigin {
    pub(crate) fn kind(self) -> &'static str {
        match self {
            ModuleOrigin::RootSource => "root_source",
            ModuleOrigin::Filesystem => "filesystem",
            ModuleOrigin::EmbeddedRuntime => "embedded_runtime",
            ModuleOrigin::PrimitivePrelude => "primitive_prelude",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum FileOrigin {
    Filesystem(PathBuf),
    EmbeddedRuntime(String),
    PrimitivePrelude(String),
}

impl FileOrigin {
    fn kind(&self) -> &'static str {
        match self {
            FileOrigin::Filesystem(_) => "filesystem",
            FileOrigin::EmbeddedRuntime(_) => "embedded_runtime",
            FileOrigin::PrimitivePrelude(_) => "primitive_prelude",
        }
    }

    fn render(&self) -> String {
        match self {
            FileOrigin::Filesystem(path) => path.display().to_string(),
            FileOrigin::EmbeddedRuntime(name) | FileOrigin::PrimitivePrelude(name) => name.clone(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ModuleState {
    Discovered,
    SourceReady,
    Parsed,
    BodySurfaceReady,
    InterfaceReady,
    MacroSurfaceReady,
    RuntimeLowered,
    RuntimePlanned,
}

impl ModuleState {
    pub(crate) fn covers(self, target: Self) -> bool {
        self >= target
    }

    fn as_str(self) -> &'static str {
        match self {
            ModuleState::Discovered => "discovered",
            ModuleState::SourceReady => "source_ready",
            ModuleState::Parsed => "parsed",
            ModuleState::BodySurfaceReady => "body_surface_ready",
            ModuleState::InterfaceReady => "interface_ready",
            ModuleState::MacroSurfaceReady => "macro_surface_ready",
            ModuleState::RuntimeLowered => "runtime_lowered",
            ModuleState::RuntimePlanned => "runtime_planned",
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
    SourceReady,
    InterfaceReady,
    SourceAndInterfaceReady,
}

#[derive(Debug, Clone)]
pub(crate) struct FunctionRecord {
    pub(crate) id: FnId,
    pub(crate) owner_module_id: ModuleId,
    pub(crate) key: FunctionKey,
    pub(crate) kind: FunctionKind,
    pub(crate) debug_name: String,
    pub(crate) contract_state: FunctionContractState,
    pub(crate) declared_source_specs: Vec<SpecDecl>,
    pub(crate) declared_interface_specs: Vec<InterfaceSpec>,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct LoweringFunctionRegistry {
    next_fn_id: u32,
    next_anonymous_id: u32,
    named_fn_ids: HashMap<Mfa, FnId>,
    new_records: Vec<FunctionRecord>,
}

impl LoweringFunctionRegistry {
    pub(crate) fn reserve_named(&mut self, owner_module_id: ModuleId, mfa: Mfa, debug_name: impl Into<String>) -> FnId {
        if let Some(existing) = self.named_fn_ids.get(&mfa).copied() {
            return existing;
        }
        let id = FnId(self.next_fn_id);
        self.next_fn_id += 1;
        self.named_fn_ids.insert(mfa.clone(), id);
        self.new_records.push(FunctionRecord {
            id,
            owner_module_id,
            key: FunctionKey::Named(mfa),
            kind: FunctionKind::Source,
            debug_name: debug_name.into(),
            contract_state: FunctionContractState::Referenced,
            declared_source_specs: Vec::new(),
            declared_interface_specs: Vec::new(),
        });
        id
    }

    pub(crate) fn fresh_anonymous(
        &mut self,
        owner_module_id: ModuleId,
        kind: FunctionKind,
        debug_name: impl Into<String>,
    ) -> FnId {
        let id = FnId(self.next_fn_id);
        self.next_fn_id += 1;
        let anonymous_id = AnonymousFunctionId(self.next_anonymous_id);
        self.next_anonymous_id += 1;
        self.new_records.push(FunctionRecord {
            id,
            owner_module_id,
            key: FunctionKey::Anonymous(anonymous_id),
            kind,
            debug_name: debug_name.into(),
            contract_state: FunctionContractState::Referenced,
            declared_source_specs: Vec::new(),
            declared_interface_specs: Vec::new(),
        });
        id
    }
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
pub(crate) struct ModuleContractRecord {
    pub(crate) interface: ModuleInterface,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum VisibleCallableAliasOrigin {
    SourceDeclaration,
    Imported {
        from_module: ModuleName,
    },
    PreludeImport {
        from_module: ModuleName,
    },
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

#[derive(Debug, Clone)]
pub(crate) struct ModuleRecord {
    pub(crate) id: ModuleId,
    pub(crate) key: ModuleKey,
    pub(crate) origin: ModuleOrigin,
    pub(crate) file_id: FileId,
    pub(crate) state: ModuleState,
    pub(crate) reachability: Reachability,
    pub(crate) body_surface: Option<ModuleBodySurface>,
    pub(crate) lowered_groups: HashMap<SourceFnKey, LoweredFnGroup>,
    pub(crate) runtime_entry_fns: HashSet<Mfa>,
    pub(crate) runtime_materialized_entry_fns: HashSet<Mfa>,
    pub(crate) runtime_lowered_functions: Option<usize>,
    pub(crate) runtime_planned_specs: Option<usize>,
    pub(crate) interfaces: Option<BTreeMap<ModuleName, ModuleInterface>>,
    pub(crate) contract: Option<ModuleContractRecord>,
    pub(crate) visible_callables: HashMap<(String, usize), VisibleCallableAlias>,
    pub(crate) macro_exports: Option<HashSet<(String, usize)>>,
    pub(crate) macro_surface: Option<ModuleMacroSurface>,
    pub(crate) prepared_prelude: Option<PreparedPrelude>,
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
    files: Vec<FileRecord>,
    functions: Vec<FunctionRecord>,
    extern_decls: Vec<ExternDecl>,
    module_index: BTreeMap<ModuleKey, ModuleId>,
    file_index: BTreeMap<FileOrigin, FileId>,
    named_function_ids: HashMap<Mfa, FnId>,
    extern_name_ids: HashMap<String, ExternId>,
    protocol_registry: ProtocolRegistry,
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
            files: Vec::new(),
            functions: Vec::new(),
            extern_decls: Vec::new(),
            module_index: BTreeMap::new(),
            file_index: BTreeMap::new(),
            named_function_ids: HashMap::new(),
            extern_name_ids: HashMap::new(),
            protocol_registry: ProtocolRegistry::default(),
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

    pub(crate) fn function_count(&self) -> usize {
        self.functions.len()
    }

    pub(crate) fn extern_count(&self) -> usize {
        self.extern_decls.len()
    }

    pub(crate) fn module(&self, id: ModuleId) -> &ModuleRecord {
        &self.modules[id.0 as usize]
    }

    pub(crate) fn file(&self, id: FileId) -> &FileRecord {
        &self.files[id.0 as usize]
    }

    pub(crate) fn function(&self, id: FnId) -> &FunctionRecord {
        &self.functions[id.0 as usize]
    }

    pub(crate) fn module_key_render(&self, id: ModuleId) -> String {
        self.modules[id.0 as usize].key.render()
    }

    pub(crate) fn module_display_name(&self, id: ModuleId) -> String {
        match &self.module(id).key {
            ModuleKey::RootPath(_) => String::new(),
            ModuleKey::Named(_) if self.module(id).origin == ModuleOrigin::PrimitivePrelude => String::new(),
            ModuleKey::Named(name) => name.dotted(),
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

    pub(crate) fn begin_lowering_function_registry(&self) -> LoweringFunctionRegistry {
        LoweringFunctionRegistry {
            next_fn_id: self.functions.len() as u32,
            next_anonymous_id: self.next_anonymous_function_id,
            named_fn_ids: self.named_function_ids.clone(),
            new_records: Vec::new(),
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
        self.functions.push(FunctionRecord {
            id,
            owner_module_id,
            key: FunctionKey::Named(mfa),
            kind: FunctionKind::Source,
            debug_name: debug_name.into(),
            contract_state: FunctionContractState::Referenced,
            declared_source_specs: Vec::new(),
            declared_interface_specs: Vec::new(),
        });
        id
    }

    pub(crate) fn commit_lowering_function_registry(&mut self, registry: LoweringFunctionRegistry) {
        let expected_start = self.functions.len() as u32;
        for (offset, record) in registry.new_records.iter().enumerate() {
            let expected = FnId(expected_start + offset as u32);
            assert_eq!(
                record.id, expected,
                "compiler function registry must append contiguous ids; expected {:?}, got {:?}",
                expected, record.id
            );
        }
        for record in &registry.new_records {
            if let FunctionKey::Named(mfa) = &record.key {
                self.named_function_ids.insert(mfa.clone(), record.id);
            }
        }
        self.next_anonymous_function_id = registry.next_anonymous_id;
        self.functions.extend(registry.new_records);
    }

    pub(crate) fn fn_id_for_mfa(&self, mfa: &Mfa) -> Option<FnId> {
        self.named_function_ids.get(mfa).copied()
    }

    pub(crate) fn function_contract_state(&self, mfa: &Mfa) -> Option<FunctionContractState> {
        let fn_id = self.fn_id_for_mfa(mfa)?;
        Some(self.function(fn_id).contract_state)
    }

    pub(crate) fn visible_callable_target(&self, module_id: ModuleId, name: &str, arity: usize) -> Option<Mfa> {
        self.module(module_id)
            .visible_callables
            .get(&(name.to_string(), arity))
            .map(|alias| alias.target.clone())
    }

    pub(crate) fn visible_callable_aliases(&self, module_id: ModuleId) -> Vec<VisibleCallableAlias> {
        let mut aliases = self.module(module_id).visible_callables.values().cloned().collect::<Vec<_>>();
        aliases.sort_by(|left, right| {
            (&left.name, left.arity, self.render_mfa(&left.target)).cmp(&(
                &right.name,
                right.arity,
                self.render_mfa(&right.target),
            ))
        });
        aliases
    }

    pub(crate) fn module_contract(&self, module_id: ModuleId) -> Option<&ModuleContractRecord> {
        self.module(module_id).contract.as_ref()
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
        ) && matches!(self.module(owner_module_id).key, ModuleKey::Named(_))
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

    fn record_visible_callable(
        &mut self,
        module_id: ModuleId,
        name: String,
        arity: usize,
        target: Mfa,
        origin: VisibleCallableAliasOrigin,
    ) {
        let key = (name, arity);
        if let Some(existing) = self.modules[module_id.0 as usize].visible_callables.get(&key) {
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
        self.modules[module_id.0 as usize].visible_callables.insert(
            key.clone(),
            VisibleCallableAlias {
                name: key.0.clone(),
                arity: key.1,
                target,
                origin,
            },
        );
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
            if !file_ids.contains(&module.file_id) {
                continue;
            }
            for target in module.visible_callables.values() {
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
            && !matches!(self.module(root_source).origin, ModuleOrigin::PrimitivePrelude)
        {
            let runtime_entry_keys = self.runtime_entry_fn_keys(root_source);
            let root_entry_keys = (!runtime_entry_keys.is_empty()).then_some(&runtime_entry_keys);
            let surface = self.ensure_body_surface(root_source, tel).map_err(|diagnostic| {
                LowerError::Unsupported {
                    span: Span::DUMMY,
                    what: diagnostic.message,
                }
            })?;
            select_initial_root_fn_keys(&surface, root_entry_keys)
        } else {
            collect_lowerable_fn_keys(self, ModuleId(u32::MAX), &prog.items)
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
        let mut prog = match resolve_program_eagerly(t, self, root_source, prog, interface_table, tel) {
            Ok(prog) => prog,
            Err(err) => {
                return Err(FrontendErr {
                    sm,
                    diagnostics: crate::diag::Diagnostics::from_one(err.to_diagnostic()),
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
            && self.module(module_id).origin == ModuleOrigin::EmbeddedRuntime
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

    pub(crate) fn ensure_module_state<F>(
        &mut self,
        module_id: ModuleId,
        target: ModuleState,
        tel: &dyn Telemetry,
        work: F,
    ) -> bool
    where
        F: FnOnce(&mut CompilerWorld),
    {
        self.world.ensure_module_state(module_id, target, tel, work)
    }

    pub(crate) fn ensure_module_state_result<F, E>(
        &mut self,
        module_id: ModuleId,
        target: ModuleState,
        tel: &dyn Telemetry,
        work: F,
    ) -> Result<bool, E>
    where
        F: FnOnce(&mut CompilerWorld) -> Result<(), E>,
    {
        self.world.ensure_module_state_result(module_id, target, tel, work)
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
    if !matches!(compiler.module(root_source).origin, ModuleOrigin::EmbeddedRuntime) {
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
    !matches!(compiler.module(root_source).origin, ModuleOrigin::EmbeddedRuntime) || planner_entry_fns.is_empty()
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
    pub(crate) fn register_root_source(
        &mut self,
        path: impl AsRef<Path>,
        src: String,
        tel: &dyn Telemetry,
    ) -> ModuleId {
        let path = path.as_ref().to_path_buf();
        self.register_module(
            ModuleKey::RootPath(path.clone()),
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

    pub(crate) fn discover_runtime_module(&mut self, module: &ModuleName, tel: &dyn Telemetry) -> Option<ModuleId> {
        let source = RUNTIME_MODULE_SOURCES
            .iter()
            .find(|candidate| candidate.name == module.dotted())?;
        Some(self.register_module(
            ModuleKey::Named(module.clone()),
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
        self.register_module(
            ModuleKey::Named(module),
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
        let _ = self.ensure_module_state(module_id, ModuleState::SourceReady, tel, |this| {
            let file_id = this.module(module_id).file_id;
            let measurements = this.state_measurements(module_id);
            let module_key = this.module(module_id).key.render();
            let module_key_kind = this.module(module_id).key.kind();
            let module_origin = this.module(module_id).origin.kind();
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
        let file_id = self.module(module_id).file_id;
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
        self.ensure_module_state_result(module_id, ModuleState::Parsed, tel, |this| {
            let file_id = this.module(module_id).file_id;
            let source = this.ensure_source(module_id, tel);
            let descriptor = this.files[file_id.0 as usize].descriptor.clone();
            let parsed = parse_source(&descriptor, &source, tel)?;
            let measurements = this.state_measurements(module_id);
            tel.execute(
                &["fz", "compiler", "parsed"],
                &measurements,
                &metadata! {
                    module_key: this.module(module_id).key.render(),
                    module_key_kind: this.module(module_id).key.kind(),
                    module_origin: this.module(module_id).origin.kind(),
                    source_name: descriptor.source_name.clone(),
                    parse_kind: parsed.parse_kind().as_str(),
                    items: parsed.item_count() as u64,
                },
            );
            this.files[file_id.0 as usize].parsed = Some(parsed);
            Ok(())
        })?;

        let file_id = self.module(module_id).file_id;
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
        let root_types = runtime_library::root_type_env_from_attrs(t, &parsed.attrs);
        let imports = collect_runtime_prelude_imports(self, tel, &parsed.items);
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
        let mut program = resolve_program_eagerly(t, self, None, staged, BTreeMap::new(), tel)
            .map_err(|err| err.to_diagnostic())?;
        program
            .module_type_envs
            .entry(String::new())
            .or_default()
            .extend_env(root_types.env);
        program.opaque_inners.extend(root_types.opaque_inners);
        program.brand_inners.extend(root_types.brand_inners);

        let prepared = PreparedPrelude { program, imports };
        for ((name, arity), qualified) in &prepared.imports {
            let Some((module_prefix, function_name)) = qualified.rsplit_once('.') else {
                continue;
            };
            let Ok(module_name) = ModuleName::parse_dotted(module_prefix) else {
                continue;
            };
            let Some(target_module_id) = self.module_id_for_name(&module_name) else {
                continue;
            };
            self.record_visible_callable(
                module_id,
                name.clone(),
                *arity,
                Mfa::new(target_module_id, function_name.to_string(), *arity),
                VisibleCallableAliasOrigin::PreludeImport {
                    from_module: module_name,
                },
            );
        }
        let module = self.module(module_id).clone();
        tel.execute(
            &["fz", "compiler", "prelude_prepared"],
            &measurements! {
                items: prepared.program.items.len() as u64,
                imports: prepared.imports.len() as u64,
                root_attrs: parsed.attrs.len() as u64,
            },
            &metadata! {
                module_key: module.key.render(),
                module_key_kind: module.key.kind(),
                module_origin: module.origin.kind(),
                source_name: self.file(module.file_id).descriptor.source_name.clone(),
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
        self.ensure_module_state_result(module_id, ModuleState::BodySurfaceReady, tel, |this| {
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
                        file_id: record.file_id.0,
                        fn_group_id: group.id.0,
                        arity: group.source.arity as u64,
                    },
                    &metadata! {
                        module_key: record.key.render(),
                        module_key_kind: record.key.kind(),
                        module_origin: record.origin.kind(),
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
                    module_key: record.key.render(),
                    module_key_kind: record.key.kind(),
                    module_origin: record.origin.kind(),
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
        self.ensure_module_state_result(module_id, ModuleState::InterfaceReady, tel, |this| {
            let _ = this.ensure_body_surface(module_id, tel)?;
            let parsed = this.ensure_parsed(module_id, tel)?;
            let interfaces = collect_interfaces(&parsed);
            this.record_module_interface_contracts(module_id, &interfaces);
            let measurements = this.state_measurements(module_id);
            tel.execute(
                &["fz", "compiler", "interface_ready"],
                &measurements,
                &metadata! {
                    module_key: this.module(module_id).key.render(),
                    module_key_kind: this.module(module_id).key.kind(),
                    module_origin: this.module(module_id).origin.kind(),
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

    pub(crate) fn discover_runtime_export_owner(
        &mut self,
        target: &ExportKey,
        tel: &dyn Telemetry,
    ) -> Result<Option<ModuleId>, Diagnostic> {
        if let Some(existing) = self.module_id_for_name(&target.module)
            && self.module(existing).origin != ModuleOrigin::EmbeddedRuntime
        {
            return Ok(None);
        }
        if let Some(owner_module) = self.protocol_callback_owners.get(target).cloned() {
            if let Some(existing) = self.module_id_for_name(&owner_module)
                && self.module(existing).origin != ModuleOrigin::EmbeddedRuntime
            {
                return Ok(None);
            }
            return Ok(self.discover_runtime_module(&owner_module, tel));
        }
        if let Some(existing) = self.module_id_for_name(&target.module) {
            if self.module(existing).origin == ModuleOrigin::EmbeddedRuntime {
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
                && self.module(existing).origin != ModuleOrigin::EmbeddedRuntime
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
        let file_id = self.module(root_id).file_id;
        let file = self.file(file_id).clone();
        for (module, interface) in &interfaces {
            let module_id = self.register_module(
                ModuleKey::Named(module.clone()),
                ModuleOrigin::Filesystem,
                file.origin.clone(),
                file.descriptor.clone(),
                tel,
            );
            let _ = self.ensure_body_surface(module_id, tel)?;
            let interface = interface.clone();
            let module = module.clone();
            let mut single = BTreeMap::new();
            single.insert(module, interface);
            let _ = self.ensure_module_state(module_id, ModuleState::InterfaceReady, tel, |this| {
                this.record_module_interface_contracts(module_id, &single);
                let measurements = this.state_measurements(module_id);
                let record = this.module(module_id);
                tel.execute(
                    &["fz", "compiler", "interface_ready"],
                    &measurements,
                    &metadata! {
                        module_key: record.key.render(),
                        module_key_kind: record.key.kind(),
                        module_origin: record.origin.kind(),
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

        let file_id = self.module(root_id).file_id;
        let file = self.file(file_id).clone();
        for (module, macros) in &exports.modules {
            let module_id = self.register_module(
                ModuleKey::Named(module.clone()),
                ModuleOrigin::Filesystem,
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
            if self.module(candidate.module_id).origin != ModuleOrigin::EmbeddedRuntime {
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
                            module_key: record.key.render(),
                            module_key_kind: record.key.kind(),
                            module_origin: record.origin.kind(),
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
                    module_key: record.key.render(),
                    module_key_kind: record.key.kind(),
                    module_origin: record.origin.kind(),
                    reason: candidate.reason,
                    from_module: candidate
                        .from_module
                        .as_ref()
                        .map(ModuleName::dotted)
                        .unwrap_or_default(),
                },
            );

            let ModuleKey::Named(module_name) = record.key.clone() else {
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
        let lowered_advanced = self.ensure_module_state(module_id, ModuleState::RuntimeLowered, tel, |_| {});
        let planned_advanced = self.ensure_module_state(module_id, ModuleState::RuntimePlanned, tel, |_| {});

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
                    file_id: record.file_id.0,
                    functions: lowered_functions as u64,
                    groups: groups,
                    units: groups,
                },
                &metadata! {
                    module_key: record.key.render(),
                    module_key_kind: record.key.kind(),
                    module_origin: record.origin.kind(),
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
                    file_id: record.file_id.0,
                    planned_specs: planned_specs as u64,
                    groups: groups,
                    units: groups,
                },
                &metadata! {
                    module_key: record.key.render(),
                    module_key_kind: record.key.kind(),
                    module_origin: record.origin.kind(),
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
        self.ensure_module_state(module_id, ModuleState::MacroSurfaceReady, tel, |this| {
            let measurements = this.state_measurements(module_id);
            let record = this.module(module_id);
            tel.execute(
                &["fz", "compiler", "macro_surface_ready"],
                &measurements,
                &metadata! {
                    module_key: record.key.render(),
                    module_key_kind: record.key.kind(),
                    module_origin: record.origin.kind(),
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
        let file_id = self.module(root_id).file_id;
        let mut items = Vec::new();
        let mut seen_fns = HashSet::new();
        let mut module_docs = HashMap::new();

        for module in &self.modules {
            if module.file_id != file_id {
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
                    module_key: record.key.render(),
                    module_key_kind: record.key.kind(),
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
                module_key: record.key.render(),
                module_key_kind: record.key.kind(),
                module_origin: record.origin.kind(),
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
            if file.source.is_some() && file.descriptor.text.is_empty() {
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
            if module.file_id.0 as usize >= self.files.len() {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` references missing file {:?}",
                    module.key.render(),
                    module.file_id
                )));
            }
            match self.module_index.get(&module.key) {
                Some(found) if *found == module.id => {}
                Some(found) => {
                    return Err(CompilerInvariantError::new(format!(
                        "module index invariant violated for `{}`: stored {:?}, indexed {:?}",
                        module.key.render(),
                        module.id,
                        found
                    )));
                }
                None => {
                    return Err(CompilerInvariantError::new(format!(
                        "module index missing entry for `{}`",
                        module.key.render()
                    )));
                }
            }

            let file = self.file(module.file_id);
            if module.state.covers(ModuleState::SourceReady) && file.source.is_none() {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` is source_ready without source text",
                    module.key.render()
                )));
            }
            if module.state.covers(ModuleState::Parsed) && file.parsed.is_none() {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` is parsed without parsed source",
                    module.key.render()
                )));
            }
            if module.state.covers(ModuleState::BodySurfaceReady) && module.body_surface.is_none() {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` is body_surface_ready without body surface",
                    module.key.render()
                )));
            }
            if module.state.covers(ModuleState::InterfaceReady) && module.interfaces.is_none() {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` is interface_ready without interface table",
                    module.key.render()
                )));
            }
            if matches!(module.key, ModuleKey::Named(_))
                && module.state.covers(ModuleState::InterfaceReady)
                && module.origin != ModuleOrigin::PrimitivePrelude
                && module.contract.is_none()
            {
                return Err(CompilerInvariantError::new(format!(
                    "named module `{}` is interface_ready without declared contract",
                    module.key.render()
                )));
            }
            if let Some(surface) = &module.body_surface {
                if surface.owner_module_id != module.id {
                    return Err(CompilerInvariantError::new(format!(
                        "module `{}` body surface owner id {:?} does not match module id {:?}",
                        module.key.render(),
                        surface.owner_module_id,
                        module.id
                    )));
                }
                let expected_owner = self.module_display_name(module.id);
                if surface.owner_module != expected_owner {
                    return Err(CompilerInvariantError::new(format!(
                        "module `{}` body surface owner `{}` does not match module owner `{}`",
                        module.key.render(),
                        surface.owner_module,
                        expected_owner
                    )));
                }
                if surface.groups.len() != surface.group_by_source.len() {
                    return Err(CompilerInvariantError::new(format!(
                        "module `{}` body surface has {} groups but {} source mappings",
                        module.key.render(),
                        surface.groups.len(),
                        surface.group_by_source.len()
                    )));
                }
                for (index, group) in surface.groups.iter().enumerate() {
                    let expected_group_id = FnGroupId(index as u32);
                    if group.id != expected_group_id {
                        return Err(CompilerInvariantError::new(format!(
                            "module `{}` body group `{}` stored id {:?}, expected {:?}",
                            module.key.render(),
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
                                module.key.render(),
                                group.qualified_name(),
                                found,
                                group.id
                            )));
                        }
                        None => {
                            return Err(CompilerInvariantError::new(format!(
                                "module `{}` body group `{}` missing source key mapping",
                                module.key.render(),
                                group.qualified_name()
                            )));
                        }
                    }
                    if !body_surface_group_belongs_to_surface(self, surface.owner_module_id, group.source.module_id) {
                        return Err(CompilerInvariantError::new(format!(
                            "module `{}` body group `{}` owner `{}` does not match surface owner `{}`",
                            module.key.render(),
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
                            module.key.render(),
                            self.render_mfa(source_key)
                        )));
                    }
                }
                let mut seen_function_ids = HashSet::new();
                for lowered in module.lowered_groups.values() {
                    if lowered.fns.len() != lowered.function_ids.len() {
                        return Err(CompilerInvariantError::new(format!(
                            "module `{}` lowered group {:?} has {} fns but {} function ids",
                            module.key.render(),
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
                            module.key.render(),
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
                            module.key.render(),
                            lowered.id,
                            descriptor.qualified_name()
                        )));
                    }
                    for (fn_ir, function_id) in lowered.fns.iter().zip(&lowered.function_ids) {
                        if fn_ir.id != *function_id {
                            return Err(CompilerInvariantError::new(format!(
                                "module `{}` lowered group {:?} stored fn {:?} but function_ids recorded {:?}",
                                module.key.render(),
                                lowered.id,
                                fn_ir.id,
                                function_id
                            )));
                        }
                        if !seen_function_ids.insert(*function_id) {
                            return Err(CompilerInvariantError::new(format!(
                                "module `{}` lowered fn {:?} belongs to more than one cached group",
                                module.key.render(),
                                function_id
                            )));
                        }
                    }
                }
            }
            if module.state == ModuleState::MacroSurfaceReady && module.macro_surface.is_none() {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` is macro_surface_ready without macro surface",
                    module.key.render()
                )));
            }
            if module.state == ModuleState::MacroSurfaceReady && !module.state.covers(ModuleState::InterfaceReady) {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` reached macro surface without interface readiness",
                    module.key.render()
                )));
            }
            if let Some(surface) = &module.macro_surface {
                if surface.program.items.iter().any(|item| !matches!(&**item, Item::Fn(_))) {
                    return Err(CompilerInvariantError::new(format!(
                        "module `{}` macro surface contains non-function items",
                        module.key.render()
                    )));
                }
            }
            if module.prepared_prelude.is_some() && module.origin != ModuleOrigin::PrimitivePrelude {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` cached prepared prelude but is not the primitive prelude",
                    module.key.render()
                )));
            }
            if module.state.covers(ModuleState::RuntimeLowered) && !module.reachability.runtime {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` reached runtime_lowered without runtime reachability",
                    module.key.render()
                )));
            }
            if module.state.covers(ModuleState::RuntimeLowered) && module.runtime_lowered_functions.is_none() {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` reached runtime_lowered without recorded lowered function facts",
                    module.key.render()
                )));
            }
            if module.state.covers(ModuleState::RuntimePlanned) && !module.state.covers(ModuleState::RuntimeLowered) {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` reached runtime_planned without runtime_lowered",
                    module.key.render()
                )));
            }
            if module.state.covers(ModuleState::RuntimePlanned) && module.runtime_planned_specs.is_none() {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` reached runtime_planned without recorded planned spec facts",
                    module.key.render()
                )));
            }
            if module.origin == ModuleOrigin::EmbeddedRuntime && !module.reachability.runtime {
                if !module.lowered_groups.is_empty() {
                    return Err(CompilerInvariantError::new(format!(
                        "runtime module `{}` cached lowered groups without runtime reachability",
                        module.key.render()
                    )));
                }
                if module.state.covers(ModuleState::RuntimeLowered) || module.state.covers(ModuleState::RuntimePlanned)
                {
                    return Err(CompilerInvariantError::new(format!(
                        "runtime module `{}` advanced execution state without runtime reachability",
                        module.key.render()
                    )));
                }
                if module.runtime_lowered_functions.is_some() || module.runtime_planned_specs.is_some() {
                    return Err(CompilerInvariantError::new(format!(
                        "runtime module `{}` recorded readiness facts without runtime reachability",
                        module.key.render()
                    )));
                }
            }
            if module.state.covers(ModuleState::RuntimeLowered) {
                for entry in &module.runtime_materialized_entry_fns {
                    if !module.lowered_groups.contains_key(entry) {
                        return Err(CompilerInvariantError::new(format!(
                            "runtime module `{}` lowered without cached entry group `{}`/{}",
                            module.key.render(),
                            self.render_mfa(entry),
                            entry.arity
                        )));
                    }
                }
            }
        }

        Ok(())
    }

    pub(crate) fn ensure_module_state<F>(
        &mut self,
        module_id: ModuleId,
        target: ModuleState,
        tel: &dyn Telemetry,
        work: F,
    ) -> bool
    where
        F: FnOnce(&mut Self),
    {
        self.ensure_module_state_result(module_id, target, tel, |this| {
            work(this);
            Ok::<(), ()>(())
        })
        .expect("infallible compiler state work failed unexpectedly")
    }

    pub(crate) fn ensure_module_state_result<F, E>(
        &mut self,
        module_id: ModuleId,
        target: ModuleState,
        tel: &dyn Telemetry,
        work: F,
    ) -> Result<bool, E>
    where
        F: FnOnce(&mut Self) -> Result<(), E>,
    {
        let current = self.module(module_id).state;
        let metadata = self.state_metadata(module_id, current, target);
        let measurements = self.state_measurements(module_id);
        if current.covers(target) {
            tel.execute(&["fz", "compiler", "cache_hit"], &measurements, &metadata);
            return Ok(false);
        }
        tel.execute(&["fz", "compiler", "cache_miss"], &measurements, &metadata);
        let _span = tel.span(&["fz", "compiler", "state_work"], metadata.clone());
        work(self)?;
        self.advance_module_state(module_id, target, tel);
        Ok(true)
    }

    fn register_module(
        &mut self,
        key: ModuleKey,
        origin: ModuleOrigin,
        file_origin: FileOrigin,
        descriptor: SourceDescriptor,
        tel: &dyn Telemetry,
    ) -> ModuleId {
        let file_id = self.intern_file(file_origin, descriptor, tel);
        if let Some(existing) = self.module_index.get(&key).copied() {
            let existing_record = self.module(existing);
            assert_eq!(
                existing_record.origin,
                origin,
                "compiler module discovery conflict for `{}`: existing origin `{}`, new origin `{}`",
                existing_record.key.render(),
                existing_record.origin.kind(),
                origin.kind()
            );
            assert_eq!(
                existing_record.file_id,
                file_id,
                "compiler module discovery conflict for `{}`: existing file {:?}, new file {:?}",
                existing_record.key.render(),
                existing_record.file_id,
                file_id
            );
            tel.execute(
                &["fz", "compiler", "module_cache_hit"],
                &measurements! { module_id: existing.0, file_id: file_id.0 },
                &metadata! {
                    module_key: existing_record.key.render(),
                    module_key_kind: existing_record.key.kind(),
                    module_origin: existing_record.origin.kind(),
                    file_origin: self.file(file_id).origin.kind(),
                },
            );
            return existing;
        }

        let id = ModuleId(self.modules.len() as u32);
        let record = ModuleRecord {
            id,
            key: key.clone(),
            origin,
            file_id,
            state: ModuleState::Discovered,
            reachability: Reachability::default(),
            body_surface: None,
            lowered_groups: HashMap::new(),
            runtime_entry_fns: HashSet::new(),
            runtime_materialized_entry_fns: HashSet::new(),
            runtime_lowered_functions: None,
            runtime_planned_specs: None,
            interfaces: None,
            contract: None,
            visible_callables: HashMap::new(),
            macro_exports: None,
            macro_surface: None,
            prepared_prelude: None,
        };
        self.modules.push(record);
        self.module_index.insert(key.clone(), id);
        tel.execute(
            &["fz", "compiler", "module_discovered"],
            &measurements! { module_id: id.0, file_id: file_id.0 },
            &metadata! {
                module_key: key.render(),
                module_key_kind: key.kind(),
                module_origin: origin.kind(),
                file_origin: self.file(file_id).origin.kind(),
            },
        );
        id
    }

    fn record_module_interface_contracts(
        &mut self,
        module_id: ModuleId,
        interfaces: &BTreeMap<ModuleName, ModuleInterface>,
    ) {
        self.record_protocol_facts_from_interfaces(interfaces);
        let ModuleKey::Named(module_name) = self.module(module_id).key.clone() else {
            return;
        };
        let Some(interface) = interfaces.get(&module_name) else {
            return;
        };
        self.modules[module_id.0 as usize].contract = Some(ModuleContractRecord {
            interface: interface.clone(),
        });
        for export in &interface.exports {
            let mfa = Mfa::new(module_id, export.name.clone(), export.arity);
            self.record_function_interface_specs(&mfa, &export.specs);
        }
    }

    fn record_protocol_facts_from_interfaces(&mut self, interfaces: &BTreeMap<ModuleName, ModuleInterface>) {
        let mut registry = ProtocolRegistry::default();
        registry.extend_interfaces(interfaces);
        self.record_protocol_facts(&registry);
    }

    pub(crate) fn record_protocol_facts(&mut self, registry: &ProtocolRegistry) {
        for (name, protocol) in &registry.protocols {
            match self.protocol_registry.protocols.get(name) {
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
                    self.protocol_registry.protocols.insert(name.clone(), protocol.clone());
                }
            }
        }

        for (key, implementation) in &registry.impls {
            match self.protocol_registry.impls.get(key) {
                Some(existing) => {
                    assert_eq!(
                        existing.callbacks, implementation.callbacks,
                        "protocol implementation callback conflict for `{}` on `{}`",
                        key.protocol, key.target
                    );
                }
                None => {
                    self.protocol_registry.impls.insert(key.clone(), implementation.clone());
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

    pub(crate) fn protocol_registry(&self) -> &ProtocolRegistry {
        &self.protocol_registry
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

    fn advance_module_state(&mut self, module_id: ModuleId, target: ModuleState, tel: &dyn Telemetry) {
        let measurements = self.state_measurements(module_id);
        let record = &mut self.modules[module_id.0 as usize];
        let from = record.state;
        debug_assert!(
            !from.covers(target),
            "advance_module_state called for {:?} from {} to {}",
            module_id,
            from.as_str(),
            target.as_str()
        );
        record.state = target;
        tel.execute(
            &["fz", "compiler", "state_advanced"],
            &measurements,
            &metadata! {
                module_key: record.key.render(),
                module_key_kind: record.key.kind(),
                module_origin: record.origin.kind(),
                from_state: from.as_str(),
                to_state: target.as_str(),
            },
        );
    }

    fn state_measurements(&self, module_id: ModuleId) -> crate::telemetry::Measurements<'static> {
        let record = self.module(module_id);
        measurements! { module_id: module_id.0, file_id: record.file_id.0 }
    }

    fn state_metadata(
        &self,
        module_id: ModuleId,
        current: ModuleState,
        target: ModuleState,
    ) -> crate::telemetry::Metadata<'static> {
        let record = self.module(module_id);
        metadata! {
            module_key: record.key.render(),
            module_key_kind: record.key.kind(),
            module_origin: record.origin.kind(),
            current_state: current.as_str(),
            target_state: target.as_str(),
        }
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
            && compiler.module(existing).origin != ModuleOrigin::EmbeddedRuntime
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

fn collect_runtime_prelude_imports(
    compiler: &mut CompilerWorld,
    tel: &dyn Telemetry,
    items: &[Rc<Item>],
) -> HashMap<(String, usize), String> {
    let mut out = HashMap::new();
    for item in items {
        match item.as_ref() {
            Item::Import {
                path,
                only,
                except,
                span,
            } => {
                collect_runtime_prelude_import(compiler, tel, &mut out, path, only.as_deref(), except.as_deref(), *span)
            }
            Item::Alias { .. } => {
                panic!("runtime.fz prelude aliases are not supported; use import")
            }
            _ => {}
        }
    }
    out
}

fn collect_runtime_prelude_import(
    compiler: &mut CompilerWorld,
    tel: &dyn Telemetry,
    out: &mut HashMap<(String, usize), String>,
    module: &ModuleName,
    only: Option<&[(String, usize)]>,
    except: Option<&[(String, usize)]>,
    span: Span,
) {
    let interface = runtime_library::interface(compiler, module, tel)
        .expect("runtime interface lookup must succeed")
        .unwrap_or_else(|| panic!("runtime.fz imports unknown built-in runtime module `{}`", module));
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
        let previous = out.insert((name.clone(), arity), format!("{}.{}", module, name));
        assert!(
            previous.is_none(),
            "runtime.fz import for `{}/{}` conflicts at {:?}",
            name,
            arity,
            span
        );
    }
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

fn collect_body_surface(
    compiler: &mut CompilerWorld,
    surface_module_id: ModuleId,
    parsed: &ParsedSource,
    tel: &dyn Telemetry,
) -> ModuleBodySurface {
    let target_module = match &compiler.module(surface_module_id).key {
        ModuleKey::RootPath(_) => None,
        ModuleKey::Named(_) if compiler.module(surface_module_id).origin == ModuleOrigin::PrimitivePrelude => None,
        ModuleKey::Named(name) => Some(name.clone()),
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
    let file = compiler.file(owner.file_id).clone();
    let origin = match owner.origin {
        ModuleOrigin::RootSource | ModuleOrigin::Filesystem => ModuleOrigin::Filesystem,
        ModuleOrigin::EmbeddedRuntime => ModuleOrigin::EmbeddedRuntime,
        ModuleOrigin::PrimitivePrelude => ModuleOrigin::PrimitivePrelude,
    };
    compiler.register_module(ModuleKey::Named(module), origin, file.origin, file.descriptor, tel)
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
        (ModuleKey::RootPath(_), _) => surface_owner.file_id == group_owner.file_id,
        (ModuleKey::Named(_), _) if surface_owner.origin == ModuleOrigin::PrimitivePrelude => {
            surface_owner.file_id == group_owner.file_id
        }
        (ModuleKey::Named(surface_name), ModuleKey::Named(group_name)) => {
            group_owner.file_id == surface_owner.file_id && module_name_matches_surface(group_name, surface_name)
        }
        (ModuleKey::Named(_), ModuleKey::RootPath(_)) => false,
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
