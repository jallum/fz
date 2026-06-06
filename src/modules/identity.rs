//! Canonical module and export identities.
//!
//! The frontend still renders many names as dotted strings because the
//! existing IR and dumps are string-shaped. These types are the semantic
//! boundary: module paths and exported functions are assembled from parsed
//! segments, not recovered by repeatedly splitting display text.

use std::error::Error;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Mfa {
    pub module: ModuleName,
    pub name: String,
    pub arity: usize,
}

impl Mfa {
    pub fn new(module: ModuleName, name: impl Into<String>, arity: usize) -> Self {
        Self {
            module,
            name: name.into(),
            arity,
        }
    }
}

impl fmt::Display for Mfa {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}/{}", self.module, self.name, self.arity)
    }
}

#[cfg(test)]
#[path = "identity_test.rs"]
mod identity_test;
