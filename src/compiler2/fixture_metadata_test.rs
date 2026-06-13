use super::fixture_metadata::{
    BudgetAssertion, EdgeAssertion, FixtureCompilerMetadata, FixtureExpect, FixtureKind, FixtureMatrixMetadata,
    FixtureMetadata, FixtureRoot, MetricAssertion, PathTimeout, parse_fixture_metadata,
};

#[test]
fn fixture_metadata_parser_ignores_sources_without_frontmatter() {
    let parsed = parse_fixture_metadata("fn main(), do: 42\n").expect("plain source should parse");
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
# paths: [jit, interp, aot, repl]
# kind: test
# expect: diagnostic
# diagnostic.code: spec/violation
# defer: waiting on compiler2
# oracle: closure.oracle.exs
# timeout.interp_secs: 15
# budget.codegen.instructions: 17
# root: main/0
# assert.metric.semantic.callsites: 2
# assert.edge: main/0[] | @66-71 | closure | main/0::lambda[@14-33]/1
# snapshot.call_edges: call_edges
#---
fn main(), do: 42
"#,
    )
    .expect("frontmatter should parse");

    assert_eq!(
        parsed,
        Some(FixtureMetadata {
            purpose: Some("closure call stays indirect".to_string()),
            matrix: FixtureMatrixMetadata {
                paths: Some(vec![
                    "jit".to_string(),
                    "interp".to_string(),
                    "aot".to_string(),
                    "repl".to_string(),
                ]),
                kind: Some(FixtureKind::Test),
                expect: Some(FixtureExpect::Diagnostic),
                diagnostic_code: Some("spec/violation".to_string()),
                defer: Some("waiting on compiler2".to_string()),
                oracle: Some("closure.oracle.exs".to_string()),
                budget_assertions: vec![BudgetAssertion {
                    name: "budget.codegen.instructions".to_string(),
                    expected: 17,
                }],
                path_timeouts: vec![PathTimeout {
                    path: "interp".to_string(),
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
fn fixture_metadata_participation_rules_are_explicit() {
    let matrix_only = parse_fixture_metadata(
        r#"#---
# purpose: runtime behaviour
# paths: [jit, interp]
#---
fn main(), do: 42
"#,
    )
    .expect("matrix-only frontmatter")
    .expect("metadata should exist");
    assert!(
        matrix_only.participates_in_matrix(),
        "paths make the fixture a behavioural matrix participant"
    );
    assert!(
        !matrix_only.participates_in_compiler_contracts(),
        "without contract keys it should stay out of compiler snapshot harnesses"
    );

    let contract_only = parse_fixture_metadata(
        r#"#---
# purpose: compiler shape
# root: main/0
# assert.metric.semantic.callsites: 1
#---
fn main(), do: 42
"#,
    )
    .expect("contract-only frontmatter")
    .expect("metadata should exist");
    assert!(
        !contract_only.participates_in_matrix(),
        "without matrix keys it should not be run by the behavioural matrix"
    );
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
fn fixture_metadata_parser_requires_well_formed_values() {
    let err = parse_fixture_metadata(
        r#"#---
# paths: jit, interp
#---
"#,
    )
    .expect_err("paths must be flow syntax");
    assert!(
        err.to_string().contains("[...]"),
        "paths shape should be explicit: {err}"
    );

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
