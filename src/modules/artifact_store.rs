//! Filesystem path policy for module artifacts.
//!
//! This module is the shared answer to "where would this module's `.fzi` or
//! `.fzo` live?" It also owns the small `.fzi` read/write helpers that use
//! that path policy.

use crate::metadata;
use crate::modules::artifact::{ArtifactFormatError, FziArtifact, FzoArtifact};
use crate::modules::identity::ModuleName;
use crate::modules::interface::ModuleInterface;
use crate::telemetry::Telemetry;
use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;
use std::fs::{create_dir_all, read_to_string, write};
use std::path::{Path, PathBuf};

pub const DEFAULT_ARTIFACT_ROOT: &str = "build/fz";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArtifactKind {
    Interface,
    Object,
}

impl ArtifactKind {
    fn directory(self) -> &'static str {
        match self {
            Self::Interface => "interfaces",
            Self::Object => "objects",
        }
    }

    fn extension(self) -> &'static str {
        match self {
            Self::Interface => "fzi",
            Self::Object => "fzo",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArtifactStore {
    root: PathBuf,
}

impl ArtifactStore {
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }

    #[cfg(test)]
    pub fn default_build() -> Self {
        Self::new(DEFAULT_ARTIFACT_ROOT)
    }

    #[cfg(test)]
    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn interface_path(&self, module: &ModuleName) -> Result<PathBuf, ArtifactPathError> {
        self.path_for(ArtifactKind::Interface, module)
    }

    pub fn object_path(&self, module: &ModuleName) -> Result<PathBuf, ArtifactPathError> {
        self.path_for(ArtifactKind::Object, module)
    }

    pub fn path_for(&self, kind: ArtifactKind, module: &ModuleName) -> Result<PathBuf, ArtifactPathError> {
        let mut path = self.root.join(kind.directory());
        let (last, parents) = module.segments().split_last().expect("ModuleName invariant: non-empty");
        for segment in parents {
            validate_path_segment(segment)?;
            path.push(segment);
        }
        validate_path_segment(last)?;
        path.push(format!("{}.{}", last, kind.extension()));
        Ok(path)
    }

    pub fn write_fzi_artifacts(
        &self,
        tel: &dyn Telemetry,
        interfaces: &BTreeMap<ModuleName, ModuleInterface>,
    ) -> Result<Vec<PathBuf>, ArtifactStoreError> {
        let mut written = Vec::new();
        for interface in interfaces.values() {
            let artifact = FziArtifact::new(interface.clone());
            let path = self.interface_path(&interface.name)?;
            if let Some(parent) = path.parent() {
                create_dir_all(parent).map_err(|source| ArtifactStoreError::Io {
                    path: parent.to_path_buf(),
                    source: source.to_string(),
                })?;
            }
            write(&path, artifact.serialize()).map_err(|source| ArtifactStoreError::Io {
                path: path.clone(),
                source: source.to_string(),
            })?;
            written.push(path);
        }
        tel.event(
            &["fz", "module", "fzi_written"],
            metadata! { modules: written.len() as i64 },
        );
        Ok(written)
    }

    pub fn write_fzo_artifacts<'a>(
        &self,
        tel: &dyn Telemetry,
        artifacts: impl IntoIterator<Item = &'a FzoArtifact>,
    ) -> Result<Vec<PathBuf>, ArtifactStoreError> {
        let mut written = Vec::new();
        for artifact in artifacts {
            let module = artifact.module.as_ref().ok_or({
                ArtifactStoreError::MissingModuleIdentity {
                    kind: ArtifactKind::Object,
                }
            })?;
            let path = self.object_path(module)?;
            write_artifact_text(&path, artifact.serialize())?;
            written.push(path);
        }
        tel.event(
            &["fz", "module", "fzo_written"],
            metadata! { modules: written.len() as i64 },
        );
        Ok(written)
    }

    pub fn load_fzi_artifact(
        &self,
        tel: &dyn Telemetry,
        module: &ModuleName,
        expected_fingerprint: Option<&[String]>,
    ) -> Result<FziArtifact, ArtifactStoreError> {
        let path = self.interface_path(module)?;
        let text = read_to_string(&path).map_err(|source| ArtifactStoreError::Io {
            path: path.clone(),
            source: source.to_string(),
        })?;
        FziArtifact::deserialize(tel, Some(&path), &text, expected_fingerprint)
            .map_err(|error| ArtifactStoreError::InvalidArtifact { path, error })
    }

    pub fn load_interface_table<'a>(
        &self,
        tel: &dyn Telemetry,
        modules: impl IntoIterator<Item = &'a ModuleName>,
    ) -> Result<BTreeMap<ModuleName, ModuleInterface>, ArtifactStoreError> {
        let modules = modules.into_iter().collect::<Vec<_>>();
        let mut table = BTreeMap::new();
        for module in &modules {
            let artifact = self.load_fzi_artifact(tel, module, None)?;
            table.insert(artifact.interface.name.clone(), artifact.interface);
        }
        if !modules.is_empty() {
            tel.event(
                &["fz", "module", "fzi_loaded"],
                metadata! { modules: modules.len() as i64 },
            );
        }
        Ok(table)
    }

    pub fn load_fzo_artifact(
        &self,
        tel: &dyn Telemetry,
        module: &ModuleName,
        expected_interface_fingerprint: Option<&[String]>,
    ) -> Result<FzoArtifact, ArtifactStoreError> {
        let path = self.object_path(module)?;
        let text = read_to_string(&path).map_err(|source| ArtifactStoreError::Io {
            path: path.clone(),
            source: source.to_string(),
        })?;
        let artifact = FzoArtifact::deserialize(tel, Some(&path), &text, expected_interface_fingerprint)
            .map_err(|error| ArtifactStoreError::InvalidArtifact { path, error })?;
        tel.event(&["fz", "module", "fzo_loaded"], metadata! { modules: 1i64 });
        Ok(artifact)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArtifactPathError {
    segment: String,
}

impl ArtifactPathError {
    #[cfg(test)]
    pub fn segment(&self) -> &str {
        &self.segment
    }
}

impl fmt::Display for ArtifactPathError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "module artifact path segment `{}` is not filesystem-safe",
            self.segment
        )
    }
}

impl Error for ArtifactPathError {}

#[derive(Debug, Clone)]
pub enum ArtifactStoreError {
    Path(ArtifactPathError),
    MissingModuleIdentity { kind: ArtifactKind },
    Io { path: PathBuf, source: String },
    InvalidArtifact { path: PathBuf, error: ArtifactFormatError },
}

impl fmt::Display for ArtifactStoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Path(err) => write!(f, "{err}"),
            Self::MissingModuleIdentity { kind } => {
                write!(f, "{} artifact has no module identity", kind.extension())
            }
            Self::Io { path, source } => write!(f, "{}: {}", path.display(), source),
            Self::InvalidArtifact { path, error } => {
                write!(f, "{}: {}", path.display(), error)
            }
        }
    }
}

impl Error for ArtifactStoreError {}

impl ArtifactStoreError {
    pub fn diagnostics_emitted(&self) -> bool {
        matches!(self, Self::InvalidArtifact { .. })
    }
}

impl From<ArtifactPathError> for ArtifactStoreError {
    fn from(value: ArtifactPathError) -> Self {
        Self::Path(value)
    }
}

fn write_artifact_text(path: &Path, text: String) -> Result<(), ArtifactStoreError> {
    if let Some(parent) = path.parent() {
        create_dir_all(parent).map_err(|source| ArtifactStoreError::Io {
            path: parent.to_path_buf(),
            source: source.to_string(),
        })?;
    }
    write(path, text).map_err(|source| ArtifactStoreError::Io {
        path: path.to_path_buf(),
        source: source.to_string(),
    })
}

fn validate_path_segment(segment: &str) -> Result<(), ArtifactPathError> {
    let valid = !segment.is_empty()
        && segment != "."
        && segment != ".."
        && segment.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_');
    if valid {
        Ok(())
    } else {
        Err(ArtifactPathError {
            segment: segment.to_string(),
        })
    }
}

#[cfg(test)]
#[path = "artifact_store_test.rs"]
mod artifact_store_test;
