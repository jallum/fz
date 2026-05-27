//! Filesystem path policy for module artifacts.
//!
//! This module deliberately does not read or write artifacts. It is the shared
//! answer to "where would this module's `.fzi` or `.fzo` live?"

use crate::module_identity::ModuleName;
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

    pub fn default_build() -> Self {
        Self::new(DEFAULT_ARTIFACT_ROOT)
    }

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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArtifactPathError {
    segment: String,
}

impl ArtifactPathError {
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
}
