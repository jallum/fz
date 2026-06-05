#![allow(dead_code)]
// fz-hua.2 makes Compiler the owner of source-backed module state, but the
// later world-model phases are still being pulled into use over the next
// tickets. Keep the allowance local to this module until those phases are live.

use crate::ast::{Attribute, FnDef, Item, ModuleDef, Program, ProtocolImplDef};
use crate::diag::{Diagnostic, SourceMap, Span};
use crate::frontend::resolve::flatten_modules_with_compiler;
use crate::fz_ir::{BlockId, ExternDecl, ExternId, ExternalCallEdge, FnId, FnIr, ProtocolCallTarget, Var};
use crate::ir_lower::{
    FnKey, LowerError, LoweringDemandResult, begin_compiler_lowering_session, collect_lowerable_fn_keys,
    select_initial_root_fn_keys,
};
use crate::modules::identity::{ExportKey, ModuleName};
use crate::modules::interface::{ModuleInterface, collect_from_program};
use crate::modules::runtime_library::{self, RUNTIME_MODULE_SOURCES, RUNTIME_PRELUDE_FZ};
use crate::parser::Parser;
use crate::parser::lexer::Lexer;
use crate::telemetry::{Telemetry, TelemetryExt as _};
use crate::types;
use crate::types::DefaultTypes;
use crate::{measurements, metadata};
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::error::Error;
use std::fmt;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ModuleId(pub u32);

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

#[derive(Debug, Clone)]
pub(crate) enum FnGroupInput {
    SourceFn(Rc<FnDef>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct SourceFnKey {
    pub(crate) owner_module: String,
    pub(crate) name: String,
    pub(crate) arity: usize,
}

impl SourceFnKey {
    pub(crate) fn new(owner_module: impl Into<String>, name: impl Into<String>, arity: usize) -> Self {
        Self {
            owner_module: owner_module.into(),
            name: name.into(),
            arity,
        }
    }

    pub(crate) fn from_qualified(name: &str, arity: usize) -> Self {
        match name.rsplit_once('.') {
            Some((owner_module, local_name)) => Self::new(owner_module.to_string(), local_name.to_string(), arity),
            None => Self::new(String::new(), name.to_string(), arity),
        }
    }

    pub(crate) fn qualified_name(&self) -> String {
        if self.owner_module.is_empty() {
            self.name.clone()
        } else {
            format!("{}.{}", self.owner_module, self.name)
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct FnGroupDescriptor {
    pub(crate) id: FnGroupId,
    pub(crate) source: SourceFnKey,
    pub(crate) is_private: bool,
    pub(crate) input: FnGroupInput,
}

impl FnGroupDescriptor {
    pub(crate) fn fn_def(&self) -> &FnDef {
        match &self.input {
            FnGroupInput::SourceFn(def) => def,
        }
    }

    pub(crate) fn qualified_name(&self) -> String {
        self.source.qualified_name()
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct ModuleBodySurface {
    pub(crate) owner_module: String,
    pub(crate) groups: Vec<FnGroupDescriptor>,
    pub(crate) group_by_source: HashMap<SourceFnKey, FnGroupId>,
}

impl ModuleBodySurface {
    fn register_source_group(&mut self, owner_module: &str, def: Rc<FnDef>) {
        let group_id = FnGroupId(self.groups.len() as u32);
        let arity = def.clauses.first().map(|clause| clause.params.len()).unwrap_or(0);
        let source = SourceFnKey::new(owner_module.to_string(), def.name.clone(), arity);
        self.groups.push(FnGroupDescriptor {
            id: group_id,
            source: source.clone(),
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
    pub(crate) module: ModuleName,
    pub(crate) entry: Option<(String, usize)>,
    pub(crate) reason: &'static str,
    pub(crate) from_module: Option<ModuleName>,
}

impl RuntimeReachabilitySeed {
    pub(crate) fn new(module: ModuleName, reason: &'static str, from_module: Option<ModuleName>) -> Self {
        Self {
            module,
            entry: None,
            reason,
            from_module,
        }
    }

    pub(crate) fn with_entry(mut self, name: impl Into<String>, arity: usize) -> Self {
        self.entry = Some((name.into(), arity));
        self
    }
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
    pub(crate) runtime_entry_fns: HashSet<(String, usize)>,
    pub(crate) interfaces: Option<BTreeMap<ModuleName, ModuleInterface>>,
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
    module_index: BTreeMap<ModuleKey, ModuleId>,
    file_index: BTreeMap<FileOrigin, FileId>,
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
            module_index: BTreeMap::new(),
            file_index: BTreeMap::new(),
        }
    }

    pub(crate) fn module_count(&self) -> usize {
        self.modules.len()
    }

    pub(crate) fn file_count(&self) -> usize {
        self.files.len()
    }

    pub(crate) fn module(&self, id: ModuleId) -> &ModuleRecord {
        &self.modules[id.0 as usize]
    }

    pub(crate) fn file(&self, id: FileId) -> &FileRecord {
        &self.files[id.0 as usize]
    }

    pub(crate) fn module_key_render(&self, id: ModuleId) -> String {
        self.modules[id.0 as usize].key.render()
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
            select_initial_root_fn_keys(&prog.items, root_entry_keys)
        } else {
            collect_lowerable_fn_keys(&prog.items)
        };

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
        session.finish(t, prog, tel)
    }
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

    pub(crate) fn module_count(&self) -> usize {
        self.world.module_count()
    }

    pub(crate) fn file_count(&self) -> usize {
        self.world.file_count()
    }

    pub(crate) fn module(&self, id: ModuleId) -> &ModuleRecord {
        self.world.module(id)
    }

    pub(crate) fn file(&self, id: FileId) -> &FileRecord {
        self.world.file(id)
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

    pub(crate) fn note_runtime_lowered(&mut self, module_id: ModuleId, fns: usize, tel: &dyn Telemetry) -> bool {
        self.world.note_runtime_lowered(module_id, fns, tel)
    }

    pub(crate) fn note_runtime_planned(
        &mut self,
        module_id: ModuleId,
        planned_specs: usize,
        tel: &dyn Telemetry,
    ) -> bool {
        self.world.note_runtime_planned(module_id, planned_specs, tel)
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
            protocol_registry: Default::default(),
            opaque_inners: Default::default(),
            brand_inners: Default::default(),
            structs: Default::default(),
            struct_field_types: Default::default(),
        };
        let mut program = flatten_modules_with_compiler(t, self, None, staged, tel).map_err(|err| err.to_diagnostic())?;
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
            let surface = collect_body_surface(&record, &parsed);
            let measurements = this.state_measurements(module_id);
            for group in &surface.groups {
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
                        owner_module: group.source.owner_module.clone(),
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
        let key = SourceFnKey::from_qualified(name, arity);
        Ok(surface.groups.into_iter().find(|group| group.source == key))
    }

    pub(crate) fn lowered_group(&self, module_id: ModuleId, source_key: &SourceFnKey) -> Option<LoweredFnGroup> {
        self.modules[module_id.0 as usize]
            .lowered_groups
            .get(source_key)
            .cloned()
    }

    pub(crate) fn runtime_entry_fn_keys(&self, module_id: ModuleId) -> HashSet<(String, usize)> {
        self.modules[module_id.0 as usize].runtime_entry_fns.clone()
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
            enqueue_runtime_interface_imports(&mut queue, interface, "program_import");
            enqueue_runtime_protocol_impl_protocols(&mut queue, interface, "program_protocol_impl");
        }
        queue.extend(seeds);

        while let Some(candidate) = queue.pop_front() {
            if let Some(existing) = self.module_id_for_name(&candidate.module)
                && self.module(existing).origin != ModuleOrigin::EmbeddedRuntime
            {
                continue;
            }
            let Some(module_id) = self.discover_runtime_module(&candidate.module, tel) else {
                continue;
            };
            if let Some(entry) = candidate.entry.clone() {
                self.modules[module_id.0 as usize].runtime_entry_fns.insert(entry);
            }
            if !self.mark_reachable(module_id, ReachabilityKind::Runtime, tel) {
                continue;
            }

            let record = self.module(module_id);
            tel.execute(
                &["fz", "compiler", "runtime_module_reachable"],
                &self.state_measurements(module_id),
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
            reachable.push(module_id);

            let interface = self
                .ensure_runtime_module_interface(&candidate.module, tel)?
                .expect("discovered runtime module must have interface");
            enqueue_runtime_interface_imports(&mut queue, &interface, "runtime_import");
            enqueue_runtime_protocol_impl_protocols(&mut queue, &interface, "runtime_protocol_impl_protocol");
            for module in runtime_library::implementation_dependencies(self, &candidate.module, tel)? {
                queue.push_back(RuntimeReachabilitySeed::new(
                    module,
                    "runtime_implementation_dependency",
                    Some(candidate.module.clone()),
                ));
            }
            enqueue_runtime_protocol_impl_providers(self, tel, &mut queue, &interface)?;
        }

        Ok(reachable)
    }

    pub(crate) fn note_runtime_lowered(&mut self, module_id: ModuleId, fns: usize, tel: &dyn Telemetry) -> bool {
        let advanced = self.ensure_module_state(module_id, ModuleState::RuntimeLowered, tel, |_| {});
        if advanced {
            let record = self.module(module_id);
            let groups = record.lowered_groups.len() as u64;
            tel.execute(
                &["fz", "compiler", "runtime_lowered"],
                &measurements! {
                    module_id: module_id.0,
                    file_id: record.file_id.0,
                    functions: fns as u64,
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
        advanced
    }

    pub(crate) fn note_runtime_planned(
        &mut self,
        module_id: ModuleId,
        planned_specs: usize,
        tel: &dyn Telemetry,
    ) -> bool {
        let advanced = self.ensure_module_state(module_id, ModuleState::RuntimePlanned, tel, |_| {});
        if advanced {
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
        advanced
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
            if let Some(surface) = &module.body_surface {
                if surface.owner_module != body_surface_owner_module(module) {
                    return Err(CompilerInvariantError::new(format!(
                        "module `{}` body surface owner `{}` does not match module owner `{}`",
                        module.key.render(),
                        surface.owner_module,
                        body_surface_owner_module(module)
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
                    if !body_surface_group_belongs_to_surface(&surface.owner_module, &group.source.owner_module) {
                        return Err(CompilerInvariantError::new(format!(
                            "module `{}` body group `{}` owner `{}` does not match surface owner `{}`",
                            module.key.render(),
                            group.qualified_name(),
                            group.source.owner_module,
                            surface.owner_module
                        )));
                    }
                }
                for source_key in module.lowered_groups.keys() {
                    if !surface.groups.iter().any(|group| &group.source == source_key) {
                        return Err(CompilerInvariantError::new(format!(
                            "module `{}` lowered group `{}` has no body-surface descriptor",
                            module.key.render(),
                            source_key.qualified_name()
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
                            lowered.source.qualified_name(),
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
            if module.state.covers(ModuleState::RuntimePlanned) && !module.state.covers(ModuleState::RuntimeLowered) {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` reached runtime_planned without runtime_lowered",
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
            }
            if module.state.covers(ModuleState::RuntimeLowered) {
                for entry in &module.runtime_entry_fns {
                    let source = SourceFnKey::from_qualified(&entry.0, entry.1);
                    if !module.lowered_groups.contains_key(&source) {
                        return Err(CompilerInvariantError::new(format!(
                            "runtime module `{}` lowered without cached entry group `{}`/{}",
                            module.key.render(),
                            source.qualified_name(),
                            source.arity
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
            interfaces: None,
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
    queue: &mut VecDeque<RuntimeReachabilitySeed>,
    interface: &ModuleInterface,
    reason: &'static str,
) {
    for import in &interface.imports {
        queue.push_back(RuntimeReachabilitySeed::new(
            import.module.clone(),
            reason,
            Some(interface.name.clone()),
        ));
    }
}

fn enqueue_runtime_protocol_impl_protocols(
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
            queue.push_back(RuntimeReachabilitySeed::new(
                protocol_impl.protocol.clone(),
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
            queue.push_back(RuntimeReachabilitySeed::new(
                module,
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
            } => collect_runtime_prelude_import(
                compiler,
                tel,
                &mut out,
                path,
                only.as_deref(),
                except.as_deref(),
                *span,
            ),
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
                protocol_registry: Default::default(),
                opaque_inners: Default::default(),
                brand_inners: Default::default(),
                structs: Default::default(),
                struct_field_types: Default::default(),
            };
            collect_from_program(&program)
        }
    }
}

fn collect_body_surface(module: &ModuleRecord, parsed: &ParsedSource) -> ModuleBodySurface {
    let owner_module = body_surface_owner_module(module);
    let mut surface = ModuleBodySurface {
        owner_module: owner_module.clone(),
        ..ModuleBodySurface::default()
    };
    match parsed {
        ParsedSource::Program(parsed) => {
            collect_body_surface_items(&parsed.program.items, "", &owner_module, &mut surface)
        }
        ParsedSource::Prelude(parsed) => collect_body_surface_items(&parsed.items, "", &owner_module, &mut surface),
    }
    surface
}

fn body_surface_owner_module(module: &ModuleRecord) -> String {
    match (&module.key, module.origin) {
        (ModuleKey::RootPath(_), _) => String::new(),
        (ModuleKey::Named(_), ModuleOrigin::PrimitivePrelude) => String::new(),
        (ModuleKey::Named(name), _) => name.dotted(),
    }
}

fn collect_body_surface_items(
    items: &[Rc<Item>],
    current_module: &str,
    owner_module: &str,
    surface: &mut ModuleBodySurface,
) {
    for item in items {
        match &**item {
            Item::Fn(def)
                if def.extern_abi.is_none()
                    && !def.is_macro
                    && (owner_module.is_empty() || current_module == owner_module) =>
            {
                surface.register_source_group(current_module, Rc::new(def.clone()));
            }
            Item::Module(module) => {
                let nested = if current_module.is_empty() {
                    module.name.clone()
                } else {
                    format!("{current_module}.{}", module.name)
                };
                collect_body_surface_items(&module.items, &nested, owner_module, surface);
            }
            Item::ProtocolImpl(protocol_impl) => {
                collect_protocol_impl_body_surface_groups(protocol_impl, items, current_module, surface);
            }
            _ => {}
        }
    }
}

fn collect_protocol_impl_body_surface_groups(
    protocol_impl: &ProtocolImplDef,
    siblings: &[Rc<Item>],
    current_module: &str,
    surface: &mut ModuleBodySurface,
) {
    let parent = module_name_from_dotted(current_module);
    let protocol = body_surface_impl_protocol_name(parent.as_ref(), &protocol_impl.protocol, siblings);
    let target = body_surface_qualify_module_child(parent.as_ref(), &protocol_impl.target.path);
    let impl_module = body_surface_protocol_impl_module(&protocol, &target).dotted();
    for item in &protocol_impl.items {
        if let Item::Fn(def) = &**item
            && def.extern_abi.is_none()
            && !def.is_macro
        {
            surface.register_source_group(&impl_module, Rc::new(def.clone()));
        }
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

fn qualify_body_surface_fn_name(owner_module: &str, fn_name: &str) -> String {
    if owner_module.is_empty() {
        fn_name.to_string()
    } else {
        format!("{owner_module}.{fn_name}")
    }
}

fn body_surface_group_belongs_to_surface(surface_owner: &str, group_owner: &str) -> bool {
    surface_owner.is_empty()
        || group_owner == surface_owner
        || group_owner
            .strip_prefix(surface_owner)
            .is_some_and(|suffix| suffix.starts_with('.'))
        || group_owner
            .strip_suffix(surface_owner)
            .is_some_and(|prefix| prefix.ends_with('.'))
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
