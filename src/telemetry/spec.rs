//! Subsystem self-description: what events a subsystem emits and what the
//! payload shape is.
//!
//! Each subsystem exposes a `pub const SPEC: Spec` listing every event
//! it might emit. The driver collects whichever specs it wants; tests collect
//! only the ones they assert on; a documentation walker can render the whole
//! catalog from the const data alone. All types are `const`-constructible so
//! a spec is fully resolved at compile time — no startup cost, no allocation.
#![allow(dead_code)]

/// A single declared key on an event's measurements or metadata.
#[derive(Debug, Clone, Copy)]
pub struct KeySpec {
    pub name: &'static str,
    pub doc: &'static str,
}

impl KeySpec {
    pub const fn new(name: &'static str, doc: &'static str) -> Self {
        Self { name, doc }
    }
}

/// One event a subsystem may emit.
#[derive(Debug, Clone, Copy)]
pub struct EventDecl {
    /// Hierarchical name as a path, e.g. `&["fz", "lexer", "tokens_built"]`.
    /// Convention: lower_snake_case segments; first segment is `fz`.
    pub name: &'static [&'static str],
    pub doc: &'static str,
    pub measurements: &'static [KeySpec],
    pub metadata: &'static [KeySpec],
}

impl EventDecl {
    pub const fn new(
        name: &'static [&'static str],
        doc: &'static str,
        measurements: &'static [KeySpec],
        metadata: &'static [KeySpec],
    ) -> Self {
        Self {
            name,
            doc,
            measurements,
            metadata,
        }
    }
}

/// A subsystem's full telemetry schema. Constructed once as a `pub const SPEC`
/// in each subsystem module.
#[derive(Debug, Clone, Copy)]
pub struct Spec {
    /// Short subsystem id, e.g. `"lexer"`, `"ir_lower"`. Used as the
    /// detach handle and to group renderer output.
    pub id: &'static str,
    pub description: &'static str,
    pub events: &'static [EventDecl],
}

impl Spec {
    pub const fn new(
        id: &'static str,
        description: &'static str,
        events: &'static [EventDecl],
    ) -> Self {
        Self {
            id,
            description,
            events,
        }
    }

    /// Find the declared event matching the given name, if any. Linear
    /// scan — specs are small (a few dozen events at most per subsystem).
    pub fn find(&self, name: &[&str]) -> Option<&EventDecl> {
        self.events.iter().find(|ev| ev.name == name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const COUNT_KEY: KeySpec = KeySpec::new("count", "number of tokens produced");
    const FN_KEY: KeySpec = KeySpec::new("fn", "fully-qualified function name");

    const TOKENS_BUILT: EventDecl = EventDecl::new(
        &["fz", "lexer", "tokens_built"],
        "Lexer completed; reports token count.",
        &[COUNT_KEY],
        &[],
    );

    const PASS_SPAN: EventDecl = EventDecl::new(
        &["fz", "lexer", "pass"],
        "Wraps a full lex pass.",
        &[],
        &[FN_KEY],
    );

    const LEXER_SPEC: Spec = Spec::new(
        "lexer",
        "Tokenizer events and spans.",
        &[TOKENS_BUILT, PASS_SPAN],
    );

    #[test]
    fn const_spec_resolves_at_compile_time() {
        assert_eq!(LEXER_SPEC.id, "lexer");
        assert_eq!(LEXER_SPEC.events.len(), 2);
        assert_eq!(LEXER_SPEC.events[0].name, &["fz", "lexer", "tokens_built"]);
        assert_eq!(LEXER_SPEC.events[0].measurements.len(), 1);
        assert_eq!(LEXER_SPEC.events[0].measurements[0].name, "count");
    }

    #[test]
    fn find_matches_exact_path() {
        let found = LEXER_SPEC.find(&["fz", "lexer", "tokens_built"]).unwrap();
        assert_eq!(found.doc, "Lexer completed; reports token count.");
    }

    #[test]
    fn find_returns_none_for_unknown_path() {
        assert!(LEXER_SPEC.find(&["fz", "lexer", "ghost"]).is_none());
        assert!(LEXER_SPEC.find(&["fz", "lexer"]).is_none());
        assert!(
            LEXER_SPEC
                .find(&["fz", "lexer", "tokens_built", "extra"])
                .is_none()
        );
    }

    #[test]
    fn key_spec_carries_doc() {
        assert_eq!(COUNT_KEY.doc, "number of tokens produced");
    }

    #[test]
    fn event_decl_doc_carries_through() {
        assert!(TOKENS_BUILT.doc.contains("token count"));
        assert!(PASS_SPAN.doc.contains("lex pass"));
    }
}
