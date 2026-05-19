//! DiagCode taxonomy (fz-ul4.20.5).
//!
//! Stable string codes for every diagnostic the fz pipeline can emit.
//! Format: `<stage>/<kind>`. Each constant is the single source of truth;
//! adding a new code lives here so the renderer + docs see it.
//!
//! Codes are introduced lazily — every entry below corresponds to an
//! existing error site that .20.7 will wire through. New codes land
//! alongside the diagnostic that needs them.

use super::diagnostic::DiagCode;

// ----- lexer -----

pub const LEX_UNEXPECTED_CHAR: DiagCode = DiagCode("lex/unexpected-char");
pub const LEX_UNTERMINATED_STRING: DiagCode = DiagCode("lex/unterminated-string");
pub const LEX_INVALID_ESCAPE: DiagCode = DiagCode("lex/invalid-escape");
pub const LEX_INVALID_NUMBER: DiagCode = DiagCode("lex/invalid-number");

// ----- parser -----

pub const PARSE_EXPECTED_TOKEN: DiagCode = DiagCode("parse/expected-token");
pub const PARSE_UNEXPECTED_TOKEN: DiagCode = DiagCode("parse/unexpected-token");
pub const PARSE_DUPLICATE_MODULEDOC: DiagCode = DiagCode("parse/duplicate-moduledoc");
pub const PARSE_DUPLICATE_DOC: DiagCode = DiagCode("parse/duplicate-doc");
pub const PARSE_DANGLING_DOC: DiagCode = DiagCode("parse/dangling-doc");
pub const PARSE_UNKNOWN_ATTRIBUTE: DiagCode = DiagCode("parse/unknown-attribute");
pub const PARSE_MACRO_CALL_SHAPE: DiagCode = DiagCode("parse/macro-call-shape");

// ----- resolver -----

pub const RESOLVE_ALIAS_OUTSIDE_MODULE: DiagCode = DiagCode("resolve/alias-outside-module");
pub const RESOLVE_IMPORT_OUTSIDE_MODULE: DiagCode = DiagCode("resolve/import-outside-module");
pub const RESOLVE_UNKNOWN_MODULE: DiagCode = DiagCode("resolve/unknown-module");
pub const RESOLVE_TYPE_ALIAS: DiagCode = DiagCode("resolve/type-alias");
pub const SPEC_VIOLATION: DiagCode = DiagCode("spec/violation");

// ----- macro expansion -----

pub const MACRO_NOT_A_DEFMACRO: DiagCode = DiagCode("macro/not-a-defmacro");
pub const MACRO_EXPANSION_LOOP: DiagCode = DiagCode("macro/expansion-loop");
pub const MACRO_ARG_REIFICATION_FAILED: DiagCode = DiagCode("macro/arg-reification-failed");
pub const MACRO_BODY_FAILED: DiagCode = DiagCode("macro/body-failed");
pub const MACRO_RETURN_DECODE_FAILED: DiagCode = DiagCode("macro/return-decode-failed");
pub const MACRO_BAD_ITEM_SHAPE: DiagCode = DiagCode("macro/bad-item-shape");
pub const MACRO_LEFTOVER_UNQUOTE: DiagCode = DiagCode("macro/leftover-unquote");

// ----- ir_lower -----

pub const LOWER_UNSUPPORTED: DiagCode = DiagCode("lower/unsupported");
pub const LOWER_UNBOUND: DiagCode = DiagCode("lower/unbound");
pub const LOWER_ARITY_MISMATCH: DiagCode = DiagCode("lower/arity-mismatch");
pub const LOWER_POST_EXPANSION_LEFTOVER: DiagCode = DiagCode("lower/post-expansion-leftover");
pub const LOWER_BACK_EDGE_TOO_MANY_ARGS: DiagCode = DiagCode("lower/back-edge-too-many-args");

// ----- typer (post-.11.24) -----

pub const TYPE_UNREACHABLE_ARM: DiagCode = DiagCode("type/unreachable-arm");
pub const TYPE_EMPTY_NARROWING: DiagCode = DiagCode("type/empty-narrowing");
pub const TYPE_NO_MATCHING_CLAUSE: DiagCode = DiagCode("type/no-matching-clause");
pub const TYPE_DEAD_BINOP: DiagCode = DiagCode("type/dead-binop");
pub const TYPE_SPEC_QUALITY: DiagCode = DiagCode("type/spec-quality");
/// fz-swt.6 — access to a field of an opaque type from outside the
/// declaring module. Emitted by the future `.value` accessor (fz-swt.8)
/// and any other opaque-field accessor that consults
/// `crate::typer::check_opaque_visibility`.
pub const TYPE_OPAQUE_VISIBILITY: DiagCode = DiagCode("type/opaque-visibility");

// fz-yxs — selective receive: matcher / guard impurity. The codegen'd
// matcher and any guard expression must stay in the pure-codegen subset
// (no allocation, no externs, no calls). See docs/receive-matched.md §2.3.
pub const TYPE_IMPURE_RECEIVE_GUARD: DiagCode = DiagCode("type/impure-receive-guard");
pub const TYPE_IMPURE_RECEIVE_PATTERN: DiagCode = DiagCode("type/impure-receive-pattern");

// ----- codegen -----

pub const CODEGEN_SCHEMA_MISSING: DiagCode = DiagCode("codegen/schema-missing");
pub const CODEGEN_TRAMPOLINE_OVERFLOW: DiagCode = DiagCode("codegen/trampoline-overflow");

// ----- runtime / interp -----

pub const RUNTIME_ASSERTION_FAILED: DiagCode = DiagCode("runtime/assertion-failed");
pub const RUNTIME_DIVISION_BY_ZERO: DiagCode = DiagCode("runtime/division-by-zero");
pub const RUNTIME_INDEX_OUT_OF_BOUNDS: DiagCode = DiagCode("runtime/index-out-of-bounds");
pub const RUNTIME_NO_MATCHING_CLAUSE: DiagCode = DiagCode("runtime/no-matching-clause");
pub const RUNTIME_BUILTIN_ERROR: DiagCode = DiagCode("runtime/builtin-error");

// ----- internal (compiler invariants) -----

pub const INTERNAL_POST_RESOLUTION_LEFTOVER: DiagCode =
    DiagCode("internal/post-resolution-leftover");
pub const INTERNAL_POST_EXPANSION_LEFTOVER: DiagCode = DiagCode("internal/post-expansion-leftover");

#[cfg(test)]
mod tests {
    use super::*;

    /// Spot-check that every code follows the `<stage>/<kind>` shape.
    /// This guards against typos creeping in as new codes get added.
    #[test]
    fn all_codes_follow_stage_slash_kind_format() {
        let codes: &[DiagCode] = &[
            LEX_UNEXPECTED_CHAR,
            LEX_UNTERMINATED_STRING,
            PARSE_EXPECTED_TOKEN,
            PARSE_UNEXPECTED_TOKEN,
            RESOLVE_ALIAS_OUTSIDE_MODULE,
            RESOLVE_IMPORT_OUTSIDE_MODULE,
            RESOLVE_TYPE_ALIAS,
            SPEC_VIOLATION,
            MACRO_NOT_A_DEFMACRO,
            MACRO_EXPANSION_LOOP,
            LOWER_UNSUPPORTED,
            LOWER_UNBOUND,
            TYPE_UNREACHABLE_ARM,
            TYPE_EMPTY_NARROWING,
            TYPE_SPEC_QUALITY,
            TYPE_OPAQUE_VISIBILITY,
            CODEGEN_SCHEMA_MISSING,
            RUNTIME_ASSERTION_FAILED,
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
