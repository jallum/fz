#![allow(dead_code)]
// fz-hua.2 makes Compiler the owner of source-backed module state, but the
// later world-model phases are still being pulled into use over the next
// tickets. Keep the allowance local to this module until those phases are live.

use crate::ast::{Attribute, FnDef, Item, ModuleDef, Program};
use crate::diag::{Diagnostic, SourceMap};
use crate::fz_ir::{FnId, FnIr};
use crate::modules::identity::ModuleName;
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

#[derive(Debug, Clone)]
pub(crate) struct FnGroupDescriptor {
    pub(crate) id: FnGroupId,
    pub(crate) owner_module: String,
    pub(crate) name: String,
    pub(crate) arity: usize,
    pub(crate) root_fn_id: FnId,
    pub(crate) is_private: bool,
    pub(crate) input: FnGroupInput,
}

impl FnGroupDescriptor {
    pub(crate) fn fn_def(&self) -> &FnDef {
        match &self.input {
            FnGroupInput::SourceFn(def) => def,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct ModuleBodySurface {
    pub(crate) owner_module: String,
    pub(crate) groups: Vec<FnGroupDescriptor>,
    pub(crate) group_by_root_fn: HashMap<FnId, FnGroupId>,
}

impl ModuleBodySurface {
    fn register_source_group(&mut self, owner_module: &str, def: Rc<FnDef>) {
        let group_id = FnGroupId(self.groups.len() as u32);
        let root_fn_id = FnId(self.groups.len() as u32);
        let arity = def.clauses.first().map(|clause| clause.params.len()).unwrap_or(0);
        self.groups.push(FnGroupDescriptor {
            id: group_id,
            owner_module: owner_module.to_string(),
            name: def.name.clone(),
            arity,
            root_fn_id,
            is_private: def.is_private,
            input: FnGroupInput::SourceFn(def),
        });
        self.group_by_root_fn.insert(root_fn_id, group_id);
    }

    pub(crate) fn group_for_root_fn(&self, root_fn_id: FnId) -> Option<FnGroupId> {
        self.group_by_root_fn.get(&root_fn_id).copied()
    }
}

#[derive(Debug, Clone)]
pub(crate) struct LoweredFnGroup {
    pub(crate) id: FnGroupId,
    pub(crate) root_fn_id: FnId,
    pub(crate) function_ids: Vec<FnId>,
    pub(crate) fns: Vec<FnIr>,
}

#[derive(Debug, Clone)]
pub(crate) struct RuntimeReachabilitySeed {
    pub(crate) module: ModuleName,
    pub(crate) reason: &'static str,
    pub(crate) from_module: Option<ModuleName>,
}

impl RuntimeReachabilitySeed {
    pub(crate) fn new(module: ModuleName, reason: &'static str, from_module: Option<ModuleName>) -> Self {
        Self {
            module,
            reason,
            from_module,
        }
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
    pub(crate) lowered_groups: HashMap<FnGroupId, LoweredFnGroup>,
    pub(crate) interfaces: Option<BTreeMap<ModuleName, ModuleInterface>>,
    pub(crate) macro_exports: Option<HashSet<(String, usize)>>,
    pub(crate) macro_surface: Option<ModuleMacroSurface>,
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

    pub(crate) fn fn_group_for_root_fn(&self, module_id: ModuleId, root_fn_id: FnId) -> Option<FnGroupId> {
        self.world.fn_group_for_root_fn(module_id, root_fn_id)
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
            let measurements = this.phase_measurements(module_id);
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
            let measurements = this.phase_measurements(module_id);
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

    pub(crate) fn ensure_body_surface(
        &mut self,
        module_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<ModuleBodySurface, Diagnostic> {
        self.ensure_module_state_result(module_id, ModuleState::BodySurfaceReady, tel, |this| {
            let parsed = this.ensure_parsed(module_id, tel)?;
            let record = this.module(module_id).clone();
            let surface = collect_body_surface(&record, &parsed);
            let measurements = this.phase_measurements(module_id);
            for group in &surface.groups {
                tel.execute(
                    &["fz", "compiler", "fn_group_discovered"],
                    &measurements! {
                        module_id: module_id.0,
                        file_id: record.file_id.0,
                        fn_group_id: group.id.0,
                        root_fn_id: group.root_fn_id.0,
                        arity: group.arity as u64,
                    },
                    &metadata! {
                        module_key: record.key.render(),
                        module_key_kind: record.key.kind(),
                        module_origin: record.origin.kind(),
                        owner_module: group.owner_module.clone(),
                        fn_name: group.name.clone(),
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
            let measurements = this.phase_measurements(module_id);
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

    pub(crate) fn fn_group_for_root_fn(&self, module_id: ModuleId, root_fn_id: FnId) -> Option<FnGroupId> {
        self.modules[module_id.0 as usize]
            .body_surface
            .as_ref()
            .and_then(|surface| surface.group_for_root_fn(root_fn_id))
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
                let measurements = this.phase_measurements(module_id);
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
            if !self.mark_reachable(module_id, ReachabilityKind::Runtime, tel) {
                continue;
            }

            let record = self.module(module_id);
            tel.execute(
                &["fz", "compiler", "runtime_module_reachable"],
                &self.phase_measurements(module_id),
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
            tel.execute(
                &["fz", "compiler", "runtime_lowered"],
                &measurements! {
                    module_id: module_id.0,
                    file_id: record.file_id.0,
                    functions: fns as u64,
                    units: 1_u64,
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
            tel.execute(
                &["fz", "compiler", "runtime_planned"],
                &measurements! {
                    module_id: module_id.0,
                    file_id: record.file_id.0,
                    planned_specs: planned_specs as u64,
                    units: 1_u64,
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
            let measurements = this.phase_measurements(module_id);
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
                &self.phase_measurements(module_id),
                &metadata! {
                    module_key: record.key.render(),
                    module_key_kind: record.key.kind(),
                    phase: "reachability",
                    reachability: kind.as_str(),
                },
            );
            return false;
        }

        let measurements = self.phase_measurements(module_id);
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
                if surface.groups.len() != surface.group_by_root_fn.len() {
                    return Err(CompilerInvariantError::new(format!(
                        "module `{}` body surface has {} groups but {} root mappings",
                        module.key.render(),
                        surface.groups.len(),
                        surface.group_by_root_fn.len()
                    )));
                }
                for (index, group) in surface.groups.iter().enumerate() {
                    let expected_group_id = FnGroupId(index as u32);
                    let expected_root_fn_id = FnId(index as u32);
                    if group.id != expected_group_id {
                        return Err(CompilerInvariantError::new(format!(
                            "module `{}` body group `{}` stored id {:?}, expected {:?}",
                            module.key.render(),
                            group.name,
                            group.id,
                            expected_group_id
                        )));
                    }
                    if group.root_fn_id != expected_root_fn_id {
                        return Err(CompilerInvariantError::new(format!(
                            "module `{}` body group `{}` stored root fn {:?}, expected {:?}",
                            module.key.render(),
                            group.name,
                            group.root_fn_id,
                            expected_root_fn_id
                        )));
                    }
                    match surface.group_by_root_fn.get(&group.root_fn_id) {
                        Some(found) if *found == group.id => {}
                        Some(found) => {
                            return Err(CompilerInvariantError::new(format!(
                                "module `{}` body group `{}` root {:?} maps to {:?} instead of {:?}",
                                module.key.render(),
                                group.name,
                                group.root_fn_id,
                                found,
                                group.id
                            )));
                        }
                        None => {
                            return Err(CompilerInvariantError::new(format!(
                                "module `{}` body group `{}` missing root fn mapping for {:?}",
                                module.key.render(),
                                group.name,
                                group.root_fn_id
                            )));
                        }
                    }
                    if group.owner_module != surface.owner_module {
                        return Err(CompilerInvariantError::new(format!(
                            "module `{}` body group `{}` owner `{}` does not match surface owner `{}`",
                            module.key.render(),
                            group.name,
                            group.owner_module,
                            surface.owner_module
                        )));
                    }
                }
                for group_id in module.lowered_groups.keys() {
                    if !surface.groups.iter().any(|group| group.id == *group_id) {
                        return Err(CompilerInvariantError::new(format!(
                            "module `{}` lowered group {:?} has no body-surface descriptor",
                            module.key.render(),
                            group_id
                        )));
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
        .expect("infallible compiler phase work failed unexpectedly")
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
        let metadata = self.phase_metadata(module_id, current, target);
        let measurements = self.phase_measurements(module_id);
        if current.covers(target) {
            tel.execute(&["fz", "compiler", "cache_hit"], &measurements, &metadata);
            return Ok(false);
        }
        tel.execute(&["fz", "compiler", "cache_miss"], &measurements, &metadata);
        let _span = tel.span(&["fz", "compiler", "phase"], metadata.clone());
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
            interfaces: None,
            macro_exports: None,
            macro_surface: None,
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
        let measurements = self.phase_measurements(module_id);
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
            &["fz", "compiler", "phase_advanced"],
            &measurements,
            &metadata! {
                module_key: record.key.render(),
                module_key_kind: record.key.kind(),
                module_origin: record.origin.kind(),
                from_phase: from.as_str(),
                to_phase: target.as_str(),
            },
        );
    }

    fn phase_measurements(&self, module_id: ModuleId) -> crate::telemetry::Measurements<'static> {
        let record = self.module(module_id);
        measurements! { module_id: module_id.0, file_id: record.file_id.0 }
    }

    fn phase_metadata(
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
            current_phase: current.as_str(),
            target_phase: target.as_str(),
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
            Item::Fn(def) if def.extern_abi.is_none() && !def.is_macro && current_module == owner_module => {
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
            _ => {}
        }
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
