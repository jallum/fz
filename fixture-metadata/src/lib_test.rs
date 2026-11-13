use super::{
    EdgeAssertion, FNV1A_OFFSET_BASIS, FixtureCompilerMetadata, FixtureExpect, FixtureKind, FixtureMatrixMetadata,
    FixtureMatrixPath, FixtureMetadata, FixtureRoot, MetricAssertion, PathDeferral, PathTimeout,
    fixture_matrix_paths_from_filename, fnv1a, oracle_stamp, parse_fixture_metadata, with_oracle_stamp,
};
use std::path::Path;

#[test]
fn fixture_metadata_parser_ignores_sources_without_frontmatter() {
    let parsed = parse_fixture_metadata("def main(), do: 42\n").expect("plain source should parse");
    assert_eq!(
        parsed, None,
        "ordinary fixtures2 sources should not need any frontmatter"
    );
}

#[test]
fn fixture_metadata_parser_reads_matrix_and_compiler_keys_together() {
    let parsed = parse_fixture_metadata(
        r#"#---
# purpose: closure call stays indirect
# kind: test
# expect: diagnostic
# diagnostic.code: spec/violation
# defer: waiting on compiler2
# defer.build: native tail delivery still red
# oracle: closure.oracle.exs
# oracle.stamp: 0123456789abcdef
# args: -- "" "é ü" --flag=1
# timeout.interp_secs: 15
# root: main/0
# assert.metric.semantic.callsites: 2
# assert.edge: main/0[] | @66-71 | closure | main/0::lambda[@14-33]/1
# snapshot.call_edges: call_edges
#---
def main(), do: 42
"#,
    )
    .expect("frontmatter should parse");

    assert_eq!(
        parsed,
        Some(FixtureMetadata {
            purpose: Some("closure call stays indirect".to_string()),
            matrix: FixtureMatrixMetadata {
                kind: Some(FixtureKind::Test),
                expect: Some(FixtureExpect::Diagnostic),
                diagnostic_code: Some("spec/violation".to_string()),
                defer: Some("waiting on compiler2".to_string()),
                path_deferrals: vec![PathDeferral {
                    path: FixtureMatrixPath::Build,
                    rationale: "native tail delivery still red".to_string(),
                }],
                oracle: Some("closure.oracle.exs".to_string()),
                oracle_stamp: Some("0123456789abcdef".to_string()),
                args: vec![
                    "--".to_string(),
                    String::new(),
                    "é ü".to_string(),
                    "--flag=1".to_string()
                ],
                path_timeouts: vec![PathTimeout {
                    path: FixtureMatrixPath::Interp,
                    seconds: 15,
                }],
            },
            compiler: FixtureCompilerMetadata {
                root: Some(FixtureRoot {
                    name: "main".to_string(),
                    arity: 0,
                }),
                metric_assertions: vec![MetricAssertion {
                    name: "semantic.callsites".to_string(),
                    expected: 2,
                }],
                edge_assertions: vec![EdgeAssertion {
                    caller: "main/0[]".to_string(),
                    callsite: "@66-71".to_string(),
                    dispatch: "closure".to_string(),
                    target: "main/0::lambda[@14-33]/1".to_string(),
                }],
                call_edge_snapshot: Some("call_edges".to_string()),
            },
        }),
        "one frontmatter block should carry both behavioural and compiler intent",
    );
}

#[test]
fn fixture_metadata_compiler_contract_participation_is_explicit() {
    let contract_only = parse_fixture_metadata(
        r#"#---
# purpose: compiler shape
# root: main/0
# assert.metric.semantic.callsites: 1
#---
def main(), do: 42
"#,
    )
    .expect("contract-only frontmatter")
    .expect("metadata should exist");
    assert!(
        contract_only.participates_in_compiler_contracts(),
        "compiler keys opt the file into compiler contract checks"
    );
}

#[test]
fn fixture_metadata_parser_rejects_unknown_and_duplicate_keys() {
    let err = parse_fixture_metadata(
        r#"#---
# purpose: one
# purpose: two
#---
"#,
    )
    .expect_err("duplicate purpose should be rejected");
    assert!(
        err.to_string().contains("may only appear once"),
        "duplicate singleton keys should fail loudly: {err}",
    );

    let err = parse_fixture_metadata(
        r#"#---
# mystery: nope
#---
"#,
    )
    .expect_err("unknown key should be rejected");
    assert!(
        err.to_string().contains("unknown fixtures2 frontmatter key"),
        "the grammar should stay explicit: {err}",
    );
}

#[test]
fn fixture_metadata_parser_rejects_budget_keys_because_nothing_checks_them() {
    // A budget line read like a compiler-shape pin while pinning nothing.
    // Shape claims are contract metrics (`assert.metric.*`) instead.
    let err = parse_fixture_metadata(
        r#"#---
# budget.codegen.functions: 34
#---
"#,
    )
    .expect_err("a budget key is not part of the grammar");
    assert!(
        err.to_string()
            .contains("unknown fixtures2 frontmatter key `budget.codegen.functions`"),
        "a budget key should fail loudly rather than pose as a pin: {err}",
    );
}

#[test]
fn fixture_metadata_parser_requires_well_formed_values() {
    let err = parse_fixture_metadata(
        r#"#---
# timeout.interp: 15
#---
"#,
    )
    .expect_err("timeout key without _secs should fail");
    assert!(
        err.to_string().contains("timeout.<path>_secs"),
        "timeout keys should stay regular: {err}",
    );

    let err = parse_fixture_metadata(
        r#"#---
# timeout.repl_secs: 15
#---
"#,
    )
    .expect_err("unsupported matrix paths should fail");
    assert!(
        err.to_string().contains("run`, `interp`, or `build"),
        "matrix path ids should stay compiler2-only: {err}",
    );

    let err = parse_fixture_metadata(
        r#"#---
# root: main
#---
"#,
    )
    .expect_err("root without arity should fail");
    assert!(
        err.to_string().contains("name/arity"),
        "root parsing should point authors at the exact required shape: {err}",
    );
}

#[test]
fn fixture_metadata_filename_routes_are_optional_and_normalized() {
    let parsed = fixture_matrix_paths_from_filename(Path::new("fixtures2/behavior/matrix_smoke.fz"))
        .expect("plain fixture stem should parse");
    assert_eq!(parsed, None, "ordinary stems use the behavioural matrix default");

    let parsed = fixture_matrix_paths_from_filename(Path::new("fixtures2/behavior/ija-matrix_smoke.fz"))
        .expect("route-prefixed stem should parse");
    assert_eq!(
        parsed,
        Some(vec![
            FixtureMatrixPath::Run,
            FixtureMatrixPath::Interp,
            FixtureMatrixPath::Build,
        ]),
        "filename route codes normalize to run/interp/build order",
    );

    let parsed = fixture_matrix_paths_from_filename(Path::new("fixtures2/00001_ja-some_fixture.fz"))
        .expect("numbered fixtures may carry route prefixes after the ordinal");
    assert_eq!(
        parsed,
        Some(vec![FixtureMatrixPath::Run, FixtureMatrixPath::Build]),
        "numbered fixture stems should discover the same route set",
    );
}

#[test]
fn fixture_metadata_filename_routes_reject_duplicate_or_unknown_codes() {
    let err = fixture_matrix_paths_from_filename(Path::new("fixtures2/behavior/iia-bad.fz"))
        .expect_err("duplicate route codes should fail");
    assert!(
        err.to_string().contains("repeats route code"),
        "duplicate filename routes should fail loudly: {err}",
    );

    let err = fixture_matrix_paths_from_filename(Path::new("fixtures2/behavior/ix-bad.fz"))
        .expect_err("unknown route codes should fail");
    assert!(
        err.to_string().contains("unknown route code"),
        "filename route grammar should stay explicit: {err}",
    );
}

#[test]
fn fixture_metadata_args_are_the_program_command_line_with_quotes_for_spaces_and_emptiness() {
    let parsed = parse_fixture_metadata("#---\n# args: a   \"b  c\" \"\"\n#---\n")
        .expect("args should parse")
        .expect("frontmatter present");
    assert_eq!(
        parsed.matrix.args,
        ["a", "b  c", ""],
        "tokens split on whitespace outside double quotes; quotes keep spaces and spell the empty argument",
    );

    let absent = parse_fixture_metadata("#---\n# purpose: x\n#---\n")
        .expect("parses")
        .expect("frontmatter present");
    assert!(
        absent.matrix.args.is_empty(),
        "a fixture without `args:` runs with no arguments"
    );
}

#[test]
fn fixture_metadata_args_reject_an_unterminated_quote_and_a_repeated_key() {
    let err = parse_fixture_metadata("#---\n# args: a \"b\n#---\n").expect_err("unterminated quote");
    assert!(err.to_string().contains("unterminated"), "{err}");

    let err = parse_fixture_metadata("#---\n# args: a\n# args: b\n#---\n").expect_err("repeated args");
    assert!(err.to_string().contains("may only appear once"), "{err}");
}

#[test]
fn fnv1a_matches_the_published_64_bit_test_vectors() {
    assert_eq!(fnv1a(FNV1A_OFFSET_BASIS, b""), 0xcbf2_9ce4_8422_2325);
    assert_eq!(fnv1a(FNV1A_OFFSET_BASIS, b"a"), 0xaf63_dc4c_8601_ec8c);
    assert_eq!(fnv1a(FNV1A_OFFSET_BASIS, b"foobar"), 0x8594_4171_f739_67e8);
}

#[test]
fn oracle_stamp_hashes_script_golden_and_each_arg_with_zero_separators() {
    let args = ["--".to_string(), String::new(), "x y".to_string()];
    assert_eq!(oracle_stamp(b"IO.puts(1)\n", b"1\n", &args), "9a6c9fb209c30ce5");
}

#[test]
fn oracle_stamp_changes_with_the_script_the_golden_or_the_args() {
    let base = oracle_stamp(b"a", b"b", &["c".to_string()]);
    assert_eq!(base.len(), 16);
    assert_ne!(base, oracle_stamp(b"A", b"b", &["c".to_string()]), "script");
    assert_ne!(base, oracle_stamp(b"a", b"B", &["c".to_string()]), "golden");
    assert_ne!(base, oracle_stamp(b"a", b"b", &["d".to_string()]), "args");
    assert_ne!(base, oracle_stamp(b"a", b"b", &[]), "arg count");
}

#[test]
fn oracle_stamp_keeps_field_boundaries_distinct() {
    assert_ne!(oracle_stamp(b"ab", b"", &[]), oracle_stamp(b"a", b"b", &[]));
    assert_ne!(
        oracle_stamp(b"", b"", &["a".to_string(), "b".to_string()]),
        oracle_stamp(b"", b"", &["ab".to_string()]),
    );
}

#[test]
fn oracle_stamp_header_key_parses_beside_oracle() {
    let parsed = parse_fixture_metadata("#---\n# oracle: oracle.exs\n# oracle.stamp: 0123456789abcdef\n#---\n")
        .expect("stamp beside oracle parses")
        .expect("frontmatter present");
    assert_eq!(parsed.matrix.oracle_stamp.as_deref(), Some("0123456789abcdef"));
}

#[test]
fn oracle_stamp_header_key_rejects_malformed_values_and_a_missing_oracle() {
    for bad in [
        "0123456789ABCDEF",
        "0123456789abcde",
        "0123456789abcdef0",
        "0123456789abcdeg",
    ] {
        let source = format!("#---\n# oracle: oracle.exs\n# oracle.stamp: {bad}\n#---\n");
        let err = parse_fixture_metadata(&source).expect_err(bad);
        assert!(err.to_string().contains("16 lowercase hex digits"), "{bad}: {err}");
    }
    let err = parse_fixture_metadata("#---\n# oracle.stamp: 0123456789abcdef\n#---\n").expect_err("no oracle");
    assert!(err.to_string().contains("requires `oracle`"), "{err}");
    let err = parse_fixture_metadata(
        "#---\n# oracle: o.exs\n# oracle.stamp: 0123456789abcdef\n# oracle.stamp: 0123456789abcdef\n#---\n",
    )
    .expect_err("repeated");
    assert!(err.to_string().contains("may only appear once"), "{err}");
}

const STAMPED_SOURCE: &str = "#---\n# purpose: p\n# oracle: oracle.exs\n# args: a\n#---\ndef main(), do: 1\n";

#[test]
fn with_oracle_stamp_inserts_the_line_after_oracle_and_changes_nothing_else() {
    let stamped = with_oracle_stamp(STAMPED_SOURCE, "0123456789abcdef").expect("stamp");
    assert_eq!(
        stamped,
        "#---\n# purpose: p\n# oracle: oracle.exs\n# oracle.stamp: 0123456789abcdef\n# args: a\n#---\ndef main(), do: 1\n"
    );
}

#[test]
fn with_oracle_stamp_replaces_an_existing_stamp_and_is_idempotent() {
    let once = with_oracle_stamp(STAMPED_SOURCE, "0123456789abcdef").expect("stamp");
    let twice = with_oracle_stamp(&once, "fedcba9876543210").expect("restamp");
    assert_eq!(twice.matches("oracle.stamp").count(), 1, "{twice}");
    assert!(twice.contains("# oracle.stamp: fedcba9876543210\n"), "{twice}");
    assert_eq!(with_oracle_stamp(&twice, "fedcba9876543210").expect("same"), twice);
    let parsed = parse_fixture_metadata(&twice).expect("parses").expect("frontmatter");
    assert_eq!(parsed.matrix.oracle_stamp.as_deref(), Some("fedcba9876543210"));
}

#[test]
fn with_oracle_stamp_refuses_a_fixture_without_an_oracle_line() {
    let err = with_oracle_stamp("#---\n# purpose: p\n#---\n", "0123456789abcdef").expect_err("no oracle");
    assert!(err.to_string().contains("requires `oracle`"), "{err}");
    assert!(with_oracle_stamp("def main(), do: 1\n", "0123456789abcdef").is_err());
}
