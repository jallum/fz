//! Filesystem path policy for module artifacts.
//!
//! This module is the shared answer to "where would this module's `.fzi` or
//! `.fzo` live?" It also owns the small `.fzi` read/write helpers that use
//! that path policy.

use crate::modules::artifact::{FziArtifact, FzoArtifact};
use crate::modules::identity::ModuleName;
use crate::modules::interface::ModuleInterface;
use std::collections::BTreeMap;
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

    pub fn path_for(
        &self,
        kind: ArtifactKind,
        module: &ModuleName,
    ) -> Result<PathBuf, ArtifactPathError> {
        let mut path = self.root.join(kind.directory());
        let (last, parents) = module
            .segments()
            .split_last()
            .expect("ModuleName invariant: non-empty");
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
        interfaces: &BTreeMap<ModuleName, ModuleInterface>,
    ) -> Result<Vec<PathBuf>, ArtifactStoreError> {
        let mut written = Vec::new();
        for interface in interfaces.values() {
            let artifact = FziArtifact::new(interface.clone());
            let path = self.interface_path(&interface.name)?;
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent).map_err(|source| ArtifactStoreError::Io {
                    path: parent.to_path_buf(),
                    source: source.to_string(),
                })?;
            }
            std::fs::write(&path, artifact.serialize()).map_err(|source| {
                ArtifactStoreError::Io {
                    path: path.clone(),
                    source: source.to_string(),
                }
            })?;
            written.push(path);
        }
        Ok(written)
    }

    pub fn write_fzi_artifacts_with_telemetry(
        &self,
        tel: &dyn crate::telemetry::Telemetry,
        interfaces: &BTreeMap<ModuleName, ModuleInterface>,
    ) -> Result<Vec<PathBuf>, ArtifactStoreError> {
        let written = self.write_fzi_artifacts(interfaces)?;
        tel.event(
            &["fz", "module", "fzi_written"],
            crate::metadata! { modules: written.len() as i64 },
        );
        Ok(written)
    }

    pub fn write_fzo_artifacts<'a>(
        &self,
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
        Ok(written)
    }

    pub fn write_fzo_artifacts_with_telemetry<'a>(
        &self,
        tel: &dyn crate::telemetry::Telemetry,
        artifacts: impl IntoIterator<Item = &'a FzoArtifact>,
    ) -> Result<Vec<PathBuf>, ArtifactStoreError> {
        let written = self.write_fzo_artifacts(artifacts)?;
        tel.event(
            &["fz", "module", "fzo_written"],
            crate::metadata! { modules: written.len() as i64 },
        );
        Ok(written)
    }

    pub fn load_fzi_artifact(
        &self,
        module: &ModuleName,
        expected_fingerprint: Option<&[String]>,
    ) -> Result<FziArtifact, ArtifactStoreError> {
        let path = self.interface_path(module)?;
        let text = std::fs::read_to_string(&path).map_err(|source| ArtifactStoreError::Io {
            path: path.clone(),
            source: source.to_string(),
        })?;
        FziArtifact::deserialize(&text, expected_fingerprint).map_err(|diagnostic| {
            ArtifactStoreError::InvalidArtifact {
                path,
                diagnostic: Box::new(diagnostic),
            }
        })
    }

    pub fn load_interface_table<'a>(
        &self,
        modules: impl IntoIterator<Item = &'a ModuleName>,
    ) -> Result<BTreeMap<ModuleName, ModuleInterface>, ArtifactStoreError> {
        let mut table = BTreeMap::new();
        for module in modules {
            let artifact = self.load_fzi_artifact(module, None)?;
            table.insert(artifact.interface.name.clone(), artifact.interface);
        }
        Ok(table)
    }

    pub fn load_interface_table_with_telemetry<'a>(
        &self,
        tel: &dyn crate::telemetry::Telemetry,
        modules: impl IntoIterator<Item = &'a ModuleName>,
    ) -> Result<BTreeMap<ModuleName, ModuleInterface>, ArtifactStoreError> {
        let modules = modules.into_iter().collect::<Vec<_>>();
        let table = self.load_interface_table(modules.iter().copied())?;
        if !modules.is_empty() {
            tel.event(
                &["fz", "module", "fzi_loaded"],
                crate::metadata! { modules: modules.len() as i64 },
            );
        }
        Ok(table)
    }

    pub fn load_fzo_artifact(
        &self,
        module: &ModuleName,
        expected_interface_fingerprint: Option<&[String]>,
    ) -> Result<FzoArtifact, ArtifactStoreError> {
        let path = self.object_path(module)?;
        let text = std::fs::read_to_string(&path).map_err(|source| ArtifactStoreError::Io {
            path: path.clone(),
            source: source.to_string(),
        })?;
        FzoArtifact::deserialize(&text, expected_interface_fingerprint).map_err(|diagnostic| {
            ArtifactStoreError::InvalidArtifact {
                path,
                diagnostic: Box::new(diagnostic),
            }
        })
    }

    #[cfg(test)]
    pub fn load_fzo_artifact_with_telemetry(
        &self,
        tel: &dyn crate::telemetry::Telemetry,
        module: &ModuleName,
        expected_interface_fingerprint: Option<&[String]>,
    ) -> Result<FzoArtifact, ArtifactStoreError> {
        let artifact = self.load_fzo_artifact(module, expected_interface_fingerprint)?;
        tel.event(
            &["fz", "module", "fzo_loaded"],
            crate::metadata! { modules: 1i64 },
        );
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

impl std::fmt::Display for ArtifactPathError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "module artifact path segment `{}` is not filesystem-safe",
            self.segment
        )
    }
}

impl std::error::Error for ArtifactPathError {}

#[derive(Debug, Clone)]
pub enum ArtifactStoreError {
    Path(ArtifactPathError),
    MissingModuleIdentity {
        kind: ArtifactKind,
    },
    Io {
        path: PathBuf,
        source: String,
    },
    InvalidArtifact {
        path: PathBuf,
        diagnostic: Box<crate::diag::Diagnostic>,
    },
}

impl std::fmt::Display for ArtifactStoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Path(err) => write!(f, "{err}"),
            Self::MissingModuleIdentity { kind } => {
                write!(f, "{} artifact has no module identity", kind.extension())
            }
            Self::Io { path, source } => write!(f, "{}: {}", path.display(), source),
            Self::InvalidArtifact { path, diagnostic } => {
                write!(f, "{}: {}", path.display(), diagnostic.message)
            }
        }
    }
}

impl std::error::Error for ArtifactStoreError {}

impl From<ArtifactPathError> for ArtifactStoreError {
    fn from(value: ArtifactPathError) -> Self {
        Self::Path(value)
    }
}

fn write_artifact_text(path: &Path, text: String) -> Result<(), ArtifactStoreError> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).map_err(|source| ArtifactStoreError::Io {
            path: parent.to_path_buf(),
            source: source.to_string(),
        })?;
    }
    std::fs::write(path, text).map_err(|source| ArtifactStoreError::Io {
        path: path.to_path_buf(),
        source: source.to_string(),
    })
}

fn validate_path_segment(segment: &str) -> Result<(), ArtifactPathError> {
    let valid = !segment.is_empty()
        && segment != "."
        && segment != ".."
        && segment
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_');
    if valid {
        Ok(())
    } else {
        Err(ArtifactPathError {
            segment: segment.to_string(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn module(segments: &[&str]) -> ModuleName {
        ModuleName::from_segments(segments.iter().map(|s| s.to_string()).collect())
    }

    #[test]
    fn default_root_is_build_fz() {
        assert_eq!(ArtifactStore::default_build().root(), Path::new("build/fz"));
    }

    #[test]
    fn top_level_module_paths_are_deterministic() {
        let store = ArtifactStore::new("out");
        let name = module(&["Utf8"]);

        assert_eq!(
            store.interface_path(&name).unwrap(),
            PathBuf::from("out/interfaces/Utf8.fzi")
        );
        assert_eq!(
            store.object_path(&name).unwrap(),
            PathBuf::from("out/objects/Utf8.fzo")
        );
    }

    #[test]
    fn nested_module_paths_preserve_segments() {
        let store = ArtifactStore::new("out");
        let name = module(&["Outer", "Inner"]);

        assert_eq!(
            store.interface_path(&name).unwrap(),
            PathBuf::from("out/interfaces/Outer/Inner.fzi")
        );
        assert_eq!(
            store.object_path(&name).unwrap(),
            PathBuf::from("out/objects/Outer/Inner.fzo")
        );
    }

    #[test]
    fn path_policy_rejects_segments_that_could_escape_root() {
        let store = ArtifactStore::new("out");
        for bad in ["..", ".", "A/B", "A\\B", "A-B", "A B", "A:B"] {
            let err = store.interface_path(&module(&["Outer", bad])).unwrap_err();
            assert_eq!(err.segment(), bad);
        }
    }

    #[test]
    fn writes_and_loads_fzi_artifacts_without_provider_source() {
        let root = std::env::temp_dir().join(format!(
            "fz-artifacts-{}-writes-and-loads-fzi",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&root);
        let store = ArtifactStore::new(&root);
        let name = module(&["Provider"]);
        let interface = ModuleInterface {
            name: name.clone(),
            abi_version: crate::modules::interface::FZ_INTERFACE_ABI_VERSION,
            imports: Vec::new(),
            exports: vec![crate::modules::interface::InterfaceFn {
                name: "id".to_string(),
                arity: 1,
                spec: None,
                name_span: crate::diag::Span::DUMMY,
            }],
            types: Vec::new(),
            docs: None,
            fingerprint_inputs: vec![
                "abi=1".to_string(),
                "module=Provider".to_string(),
                "fn=id/1:<unspecified>".to_string(),
            ],
        };
        let mut interfaces = BTreeMap::new();
        interfaces.insert(name.clone(), interface.clone());

        let written = store.write_fzi_artifacts(&interfaces).unwrap();
        assert_eq!(written, vec![root.join("interfaces/Provider.fzi")]);

        let loaded = store.load_interface_table([&name]).unwrap();
        assert_eq!(loaded.get(&name), Some(&interface));

        let _ = std::fs::remove_dir_all(&root);
    }
}
