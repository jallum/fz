//! DiagCode taxonomy (fz-ul4.20.5).
//!
//! Stable string codes for diagnostics the fz pipeline emits now.
//! Format: `<stage>/<kind>`. New codes land with the diagnostic site
//! that emits them.

pub use super::diagnostic::DiagCode;

// ----- parser -----

pub const PARSE_EXPECTED_TOKEN: DiagCode = DiagCode("parse/expected-token");
pub const PARSE_DANGLING_FUNCTION_ATTR: DiagCode = DiagCode("parse/dangling-function-attr");

// ----- resolver -----

pub const RESOLVE_UNKNOWN_MODULE: DiagCode = DiagCode("resolve/unknown-module");
pub const RESOLVE_UNKNOWN_FUNCTION: DiagCode = DiagCode("resolve/unknown-function");
pub const RESOLVE_UNKNOWN_IMPORT: DiagCode = DiagCode("resolve/unknown-import");
pub const RESOLVE_TYPE_ALIAS: DiagCode = DiagCode("resolve/type-alias");

// ----- macro expansion -----

pub const MACRO_NOT_A_DEFMACRO: DiagCode = DiagCode("macro/not-a-defmacro");
pub const MACRO_NOT_REQUIRED: DiagCode = DiagCode("macro/not-required");

// ----- ir_lower -----

pub const LOWER_UNSUPPORTED: DiagCode = DiagCode("lower/unsupported");
pub const LOWER_UNBOUND: DiagCode = DiagCode("lower/unbound");

// ----- planner (post-.11.24) -----

pub const TYPE_NO_MATCHING_CLAUSE: DiagCode = DiagCode("type/no-matching-clause");
pub const TYPE_NUMERIC_LITERAL_WIDENED: DiagCode = DiagCode("type/numeric-literal-widened");

// ----- codegen -----

pub const ARTIFACT_INCOMPLETE_SEMANTIC_PLAN: DiagCode = DiagCode("artifact/incomplete-semantic-plan");

// ----- internal (compiler invariants) -----

pub const INTERNAL_POST_RESOLUTION_LEFTOVER: DiagCode = DiagCode("internal/post-resolution-leftover");

#[cfg(test)]
#[path = "codes_test.rs"]
mod codes_test;
