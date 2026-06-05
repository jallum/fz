#![allow(dead_code)]
// fz-hua.1 defines the compiler world model before fz-hua.2 wires source
// loading and phase advancement through it. Keep the allowance local to this
// module; remove it as the new path takes over.

use crate::modules::identity::ModuleName;
use crate::telemetry::{Telemetry, TelemetryExt as _};
use crate::types;
use crate::types::DefaultTypes;
use crate::{measurements, metadata};
use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;
use std::path::PathBuf;

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

#[derive(Debug, Clone)]
pub(crate) struct ModuleRecord {
    pub(crate) id: ModuleId,
    pub(crate) key: ModuleKey,
    pub(crate) origin: ModuleOrigin,
    pub(crate) file_id: FileId,
    pub(crate) state: ModuleState,
    pub(crate) reachability: Reachability,
}

#[derive(Debug, Clone)]
pub(crate) struct FileRecord {
    pub(crate) id: FileId,
    pub(crate) origin: FileOrigin,
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

pub(crate) struct Compiler {
    types: DefaultTypes,
    modules: Vec<ModuleRecord>,
    files: Vec<FileRecord>,
    module_index: BTreeMap<ModuleKey, ModuleId>,
    file_index: BTreeMap<FileOrigin, FileId>,
}

impl Compiler {
    pub(crate) fn new() -> Self {
        Self {
            types: types::new(),
            modules: Vec::new(),
            files: Vec::new(),
            module_index: BTreeMap::new(),
            file_index: BTreeMap::new(),
        }
    }

    pub(crate) fn types(&mut self) -> &mut DefaultTypes {
        &mut self.types
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

    pub(crate) fn discover_module(
        &mut self,
        key: ModuleKey,
        origin: ModuleOrigin,
        file_origin: FileOrigin,
        tel: &dyn Telemetry,
    ) -> ModuleId {
        let file_id = self.intern_file(file_origin, tel);
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
        let current = self.module(module_id).state;
        let metadata = self.phase_metadata(module_id, current, target);
        let measurements = self.phase_measurements(module_id);
        if current.covers(target) {
            tel.execute(&["fz", "compiler", "cache_hit"], &measurements, &metadata);
            return false;
        }
        tel.execute(&["fz", "compiler", "cache_miss"], &measurements, &metadata);
        let _span = tel.span(&["fz", "compiler", "phase"], metadata.clone());
        work(self);
        self.advance_module_state(module_id, target, tel);
        true
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

    fn intern_file(&mut self, origin: FileOrigin, tel: &dyn Telemetry) -> FileId {
        if let Some(existing) = self.file_index.get(&origin).copied() {
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

#[cfg(test)]
#[path = "compiler_test.rs"]
mod compiler_test;
