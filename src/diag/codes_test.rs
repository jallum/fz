use super::*;

/// Spot-check that every code follows the `<stage>/<kind>` shape.
/// This guards against typos creeping in as new codes get added.
#[test]
fn all_codes_follow_stage_slash_kind_format() {
    let codes: &[DiagCode] = &[
        LEX_UNEXPECTED_CHAR,
        PARSE_EXPECTED_TOKEN,
        RESOLVE_DUPLICATE_MODULE,
        RESOLVE_DUPLICATE_EXPORT,
        RESOLVE_UNKNOWN_MODULE,
        RESOLVE_UNKNOWN_IMPORT,
        RESOLVE_CONFLICTING_IMPORT,
        RESOLVE_TYPE_ALIAS,
        RESOLVE_PROTOCOL,
        INTERFACE_MISSING_SPEC,
        SPEC_VIOLATION,
        MACRO_NOT_A_DEFMACRO,
        MACRO_EXPANSION_LOOP,
        LOWER_UNSUPPORTED,
        LOWER_UNBOUND,
        TYPE_UNREACHABLE_ARM,
        TYPE_OPAQUE_VISIBILITY,
        TYPE_EXTERN_MARSHAL,
        CODEGEN_SCHEMA_MISSING,
        ARTIFACT_INVALID,
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
