//! DiagCode taxonomy (fz-ul4.20.5).
//!
//! Stable string codes for diagnostics the fz pipeline emits now.
//! Format: `<stage>/<kind>`. New codes land with the diagnostic site
//! that emits them.

use super::diagnostic::DiagCode;

// ----- lexer -----

pub const LEX_UNEXPECTED_CHAR: DiagCode = DiagCode("lex/unexpected-char");

// ----- parser -----

pub const PARSE_EXPECTED_TOKEN: DiagCode = DiagCode("parse/expected-token");

// ----- resolver -----

pub const RESOLVE_ALIAS_OUTSIDE_MODULE: DiagCode = DiagCode("resolve/alias-outside-module");
pub const RESOLVE_IMPORT_OUTSIDE_MODULE: DiagCode = DiagCode("resolve/import-outside-module");
pub const RESOLVE_DUPLICATE_MODULE: DiagCode = DiagCode("resolve/duplicate-module");
pub const RESOLVE_DUPLICATE_EXPORT: DiagCode = DiagCode("resolve/duplicate-export");
pub const RESOLVE_TYPE_ALIAS: DiagCode = DiagCode("resolve/type-alias");
pub const SPEC_VIOLATION: DiagCode = DiagCode("spec/violation");

// ----- macro expansion -----

pub const MACRO_NOT_A_DEFMACRO: DiagCode = DiagCode("macro/not-a-defmacro");
pub const MACRO_EXPANSION_LOOP: DiagCode = DiagCode("macro/expansion-loop");
pub const MACRO_ARG_REIFICATION_FAILED: DiagCode = DiagCode("macro/arg-reification-failed");
pub const MACRO_BODY_FAILED: DiagCode = DiagCode("macro/body-failed");
pub const MACRO_RETURN_DECODE_FAILED: DiagCode = DiagCode("macro/return-decode-failed");

// ----- ir_lower -----

pub const LOWER_UNSUPPORTED: DiagCode = DiagCode("lower/unsupported");
pub const LOWER_UNBOUND: DiagCode = DiagCode("lower/unbound");
pub const LOWER_POST_EXPANSION_LEFTOVER: DiagCode = DiagCode("lower/post-expansion-leftover");

// ----- planner (post-.11.24) -----

pub const TYPE_UNREACHABLE_ARM: DiagCode = DiagCode("type/unreachable-arm");
pub const TYPE_NO_MATCHING_CLAUSE: DiagCode = DiagCode("type/no-matching-clause");
pub const TYPE_DEAD_BINOP: DiagCode = DiagCode("type/dead-binop");
/// fz-swt.6 — access to a field of an opaque type from outside the
/// declaring module. Emitted by the future `.value` accessor (fz-swt.8)
/// and any other opaque-field accessor that consults
/// `crate::ir_planner::check_opaque_visibility`.
pub const TYPE_OPAQUE_VISIBILITY: DiagCode = DiagCode("type/opaque-visibility");

/// fz-l4c — arithmetic operator applied to an operand whose declared
/// type is opaque. Opaque types (`pid`, `ref`, user `opaque` aliases)
/// are nominally disjoint from `int` / `float`; allowing `pid + 1` to
/// "work" because of the underlying bit-tagging is a soundness leak.
/// Comparison (`==`, `!=`) remains permitted — pid/ref equality is
/// load-bearing for the selective-receive matcher.
pub const TYPE_OPAQUE_ARITHMETIC: DiagCode = DiagCode("type/opaque-arithmetic");

// fz-yxs — selective receive: matcher / guard impurity. The codegen'd
// matcher and any guard expression must stay in the pure-codegen subset
// (no allocation, no externs, no calls). See docs/receive-matched.md §2.3.
pub const TYPE_IMPURE_RECEIVE_GUARD: DiagCode = DiagCode("type/impure-receive-guard");
// fz-puj.30 (G1) — FnCategory::Matcher fns own matcher dispatch
// for case / multi-clause / with-else / receive. They must stay pure
// (no allocation, no extern) so they can be safely inlined back at
// trivial sites and reasoned about as side-effect-free routers.
pub const TYPE_IMPURE_MATCHER: DiagCode = DiagCode("type/impure-matcher");

// ----- codegen -----

pub const CODEGEN_SCHEMA_MISSING: DiagCode = DiagCode("codegen/schema-missing");

// ----- internal (compiler invariants) -----

pub const INTERNAL_POST_RESOLUTION_LEFTOVER: DiagCode =
    DiagCode("internal/post-resolution-leftover");

#[cfg(test)]
mod tests {
    use super::*;

    /// Spot-check that every code follows the `<stage>/<kind>` shape.
    /// This guards against typos creeping in as new codes get added.
    #[test]
    fn all_codes_follow_stage_slash_kind_format() {
        let codes: &[DiagCode] = &[
            LEX_UNEXPECTED_CHAR,
            PARSE_EXPECTED_TOKEN,
            RESOLVE_ALIAS_OUTSIDE_MODULE,
            RESOLVE_IMPORT_OUTSIDE_MODULE,
            RESOLVE_DUPLICATE_MODULE,
            RESOLVE_DUPLICATE_EXPORT,
            RESOLVE_TYPE_ALIAS,
            SPEC_VIOLATION,
            MACRO_NOT_A_DEFMACRO,
            MACRO_EXPANSION_LOOP,
            LOWER_UNSUPPORTED,
            LOWER_UNBOUND,
            TYPE_UNREACHABLE_ARM,
            TYPE_OPAQUE_VISIBILITY,
            CODEGEN_SCHEMA_MISSING,
            INTERNAL_POST_RESOLUTION_LEFTOVER,
        ];
        for c in codes {
            let parts: Vec<_> = c.0.split('/').collect();
            assert_eq!(parts.len(), 2, "code {} must be stage/kind", c.0);
            assert!(
                !parts[0].is_empty() && !parts[1].is_empty(),
                "both halves of {} must be non-empty",
                c.0
            );
            // Kebab-case after the slash.
            assert!(
                parts[1].chars().all(|c| c.is_ascii_lowercase() || c == '-'),
                "kind half of {} should be kebab-case",
                c.0
            );
        }
    }
}
