//! Canonical module and export identities.
//!
//! The frontend still renders many names as dotted strings because the
//! existing IR and dumps are string-shaped. These types are the semantic
//! boundary: module paths and exported functions are assembled from parsed
//! segments, not recovered by repeatedly splitting display text.

use std::error::Error;
use std::fmt;

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ModuleName {
    segments: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleNameParseError {
    text: String,
}

impl ModuleName {
    pub fn from_segments(segments: Vec<String>) -> Self {
        assert!(!segments.is_empty(), "ModuleName must have at least one segment");
        assert!(
            segments.iter().all(|s| !s.is_empty()),
            "ModuleName segments must be non-empty"
        );
        Self { segments }
    }

    pub fn parse_dotted(text: &str) -> Result<Self, ModuleNameParseError> {
        let segments = text.split('.').map(str::to_string).collect::<Vec<_>>();
        if segments.is_empty() || segments.iter().any(|segment| segment.is_empty()) {
            Err(ModuleNameParseError { text: text.to_string() })
        } else {
            Ok(Self { segments })
        }
    }

    pub fn child(&self, segment: impl Into<String>) -> Self {
        let mut segments = self.segments.clone();
        let segment = segment.into();
        assert!(!segment.is_empty(), "ModuleName child must be non-empty");
        segments.push(segment);
        Self { segments }
    }

    pub fn segments(&self) -> &[String] {
        &self.segments
    }

    pub fn last_segment(&self) -> &str {
        self.segments.last().expect("ModuleName invariant: non-empty")
    }

    /// Display spelling used by current IR/debug output. Do not use this as
    /// the source of truth when a typed `ModuleName` is available.
    pub fn dotted(&self) -> String {
        self.segments().join(".")
    }
}

impl fmt::Display for ModuleName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.dotted())
    }
}

impl fmt::Display for ModuleNameParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid module name `{}`", self.text)
    }
}

impl Error for ModuleNameParseError {}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct QualifiedName {
    pub module: Option<ModuleName>,
    pub name: String,
}

impl QualifiedName {
    pub fn in_module(module: ModuleName, name: impl Into<String>) -> Self {
        Self {
            module: Some(module),
            name: name.into(),
        }
    }

    /// Display spelling used by current flattened IR names.
    pub fn dotted(&self) -> String {
        match &self.module {
            Some(module) => format!("{}.{}", module, self.name),
            None => self.name.clone(),
        }
    }
}

impl fmt::Display for QualifiedName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.dotted())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Mfa {
    pub qualified: QualifiedName,
    pub arity: usize,
}

impl Mfa {
    pub fn new(module: Option<ModuleName>, name: impl Into<String>, arity: usize) -> Self {
        Self {
            qualified: QualifiedName {
                module,
                name: name.into(),
            },
            arity,
        }
    }

    pub fn in_module(module: ModuleName, name: impl Into<String>, arity: usize) -> Self {
        Self::new(Some(module), name, arity)
    }

    pub fn top_level(name: impl Into<String>, arity: usize) -> Self {
        Self::new(None, name, arity)
    }

    pub fn from_qualified(text: &str, arity: usize) -> Self {
        match text.rsplit_once('.') {
            Some((module, name)) => {
                let module = ModuleName::parse_dotted(module).expect("qualified MFA module name must parse");
                Self::in_module(module, name.to_string(), arity)
            }
            None => Self::top_level(text.to_string(), arity),
        }
    }

    pub fn module(&self) -> Option<&ModuleName> {
        self.qualified.module.as_ref()
    }

    pub fn module_dotted(&self) -> String {
        self.module().map(ModuleName::dotted).unwrap_or_default()
    }

    pub fn qualified_name(&self) -> String {
        self.qualified.dotted()
    }
}

impl fmt::Display for Mfa {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.qualified, self.arity)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ExportKey {
    pub module: ModuleName,
    pub name: String,
    pub arity: usize,
}

impl ExportKey {
    pub fn new(module: ModuleName, name: impl Into<String>, arity: usize) -> Self {
        Self {
            module,
            name: name.into(),
            arity,
        }
    }
}

impl fmt::Display for ExportKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}/{}", self.module, self.name, self.arity)
    }
}

#[cfg(test)]
#[path = "identity_test.rs"]
mod identity_test;
