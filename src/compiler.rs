#![allow(dead_code)]
// fz-hua.2 makes Compiler the owner of source-backed module state, but the
// later world-model phases are still being pulled into use over the next
// tickets. Keep the allowance local to this module until those phases are live.

use crate::ast::{Attribute, Item, Program};
use crate::diag::{Diagnostic, SourceMap};
use crate::modules::identity::ModuleName;
use crate::modules::interface::{ModuleInterface, collect_from_program};
use crate::modules::runtime_library::{RUNTIME_MODULE_SOURCES, RUNTIME_PRELUDE_FZ};
use crate::parser::Parser;
use crate::parser::lexer::Lexer;
use crate::telemetry::{Telemetry, TelemetryExt as _};
use crate::types;
use crate::types::DefaultTypes;
use crate::{measurements, metadata};
use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ModuleId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct FileId(pub u32);

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
    fn kind(self) -> &'static str {
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
pub(crate) struct ModuleRecord {
    pub(crate) id: ModuleId,
    pub(crate) key: ModuleKey,
    pub(crate) origin: ModuleOrigin,
    pub(crate) file_id: FileId,
    pub(crate) state: ModuleState,
    pub(crate) reachability: Reachability,
    pub(crate) interfaces: Option<BTreeMap<ModuleName, ModuleInterface>>,
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

    pub(crate) fn ensure_runtime_module_interface(
        &mut self,
        module: &ModuleName,
        tel: &dyn Telemetry,
    ) -> Result<Option<ModuleInterface>, Diagnostic> {
        self.world.ensure_runtime_module_interface(module, tel)
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

    pub(crate) fn ensure_source(&mut self, module_id: ModuleId, tel: &dyn Telemetry) -> Arc<str> {
        let _ = self.ensure_module_state(module_id, ModuleState::SourceReady, tel, |this| {
            let file_id = this.module(module_id).file_id;
            let measurements = this.phase_measurements(module_id);
            let record = &mut this.files[file_id.0 as usize];
            let source = record.descriptor.text.clone();
            record.source = Some(source.clone());
            tel.execute(
                &["fz", "compiler", "source_loaded"],
                &measurements,
                &metadata! {
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

    pub(crate) fn ensure_interface_table(
        &mut self,
        module_id: ModuleId,
        tel: &dyn Telemetry,
    ) -> Result<BTreeMap<ModuleName, ModuleInterface>, Diagnostic> {
        self.ensure_module_state_result(module_id, ModuleState::InterfaceReady, tel, |this| {
            let parsed = this.ensure_parsed(module_id, tel)?;
            let interfaces = collect_interfaces(&parsed);
            let measurements = this.phase_measurements(module_id);
            tel.execute(
                &["fz", "compiler", "interface_ready"],
                &measurements,
                &metadata! {
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
            if module.state.covers(ModuleState::InterfaceReady) && module.interfaces.is_none() {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` is interface_ready without interface table",
                    module.key.render()
                )));
            }
            if module.state.covers(ModuleState::MacroSurfaceReady) && !module.state.covers(ModuleState::InterfaceReady)
            {
                return Err(CompilerInvariantError::new(format!(
                    "module `{}` reached macro surface without interface readiness",
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
            interfaces: None,
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

#[cfg(test)]
#[path = "compiler_test.rs"]
mod compiler_test;
