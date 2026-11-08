//! Parsed module identity, independent of compiler and runtime numbering.
use std::error::Error;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ModuleName {
    segments: Vec<String>,
}

/// A module's source denotation. Implementation ownership includes the boundary
/// between protocol and target; its display path is not a named module lookup.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ModuleDenotation {
    Named(ModuleName),
    ProtocolImpl { protocol: ModuleName, target: ModuleName },
}

impl ModuleDenotation {
    /// Structural term encoding shared by compiler reflection and quote
    /// reification. Each path remains a separate ordered field.
    pub fn quoted_parts(&self) -> (&'static str, impl Iterator<Item = &ModuleName>) {
        let (tag, first, second) = match self {
            Self::Named(name) => ("named", name, None),
            Self::ProtocolImpl { protocol, target } => ("protocol_impl", protocol, Some(target)),
        };
        (tag, std::iter::once(first).chain(second))
    }

    pub fn named_path(&self) -> Option<&ModuleName> {
        match self {
            Self::Named(name) => Some(name),
            Self::ProtocolImpl { .. } => None,
        }
    }

    /// Source-visible alias spelling for quoted environment and diagnostic data.
    /// Never use this projection to recover a module's identity.
    pub fn display_segments(&self) -> impl Iterator<Item = &String> {
        let (first, second) = match self {
            Self::Named(name) => (name, None),
            Self::ProtocolImpl { protocol, target } => (protocol, Some(target)),
        };
        first
            .segments()
            .iter()
            .chain(second.into_iter().flat_map(ModuleName::segments))
    }
}

impl fmt::Display for ModuleDenotation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Named(name) => name.fmt(f),
            Self::ProtocolImpl { protocol, target } => write!(f, "{protocol}.{target}"),
        }
    }
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

    /// The atom this module name is in value position: `Foo.Bar` is the atom
    /// `Elixir.Foo.Bar`, as in Elixir.
    pub fn atom_name(&self) -> String {
        format!("{ALIAS_ATOM_ROOT}.{}", self.dotted())
    }
}

/// The field a struct answers with its own module: `p.__struct__`.
pub const STRUCT_MODULE_FIELD: &str = "__struct__";

/// The root every module-name atom hangs from.
const ALIAS_ATOM_ROOT: &str = "Elixir";

/// Whether an atom lives in the module-name namespace: its name starts with
/// `Elixir.`. Elixir never prints such an atom as a keyword key.
pub fn is_alias_namespace_atom(atom_name: &str) -> bool {
    atom_name
        .strip_prefix(ALIAS_ATOM_ROOT)
        .is_some_and(|rest| rest.starts_with('.'))
}

/// The alias an atom prints as, when its name is shaped like a module name:
/// `Elixir` followed by `.`-separated segments, each an ASCII capital letter
/// and then ASCII letters, digits or `_`. `Elixir.Foo.Bar` prints as `Foo.Bar`
/// and `Elixir` as itself; `Elixir.foo` and `Elixir.Foo?` have no alias.
pub fn alias_spelling(atom_name: &str) -> Option<&str> {
    let rest = atom_name.strip_prefix(ALIAS_ATOM_ROOT)?;
    if rest.is_empty() {
        return Some(atom_name);
    }
    let path = rest.strip_prefix('.')?;
    path.split('.').all(is_alias_segment).then_some(path)
}

fn is_alias_segment(segment: &str) -> bool {
    let mut chars = segment.chars();
    chars.next().is_some_and(|first| first.is_ascii_uppercase()) && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
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

#[cfg(test)]
#[path = "module_name_test.rs"]
mod module_name_test;
