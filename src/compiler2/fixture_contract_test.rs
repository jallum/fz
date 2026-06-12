use super::fixture_contract::{EdgeAssertion, FixtureContract, FixtureRoot, MetricAssertion, parse_fixture_contract};

#[test]
fn fixture_contract_parser_ignores_sources_without_contract_frontmatter() {
    let parsed = parse_fixture_contract("fn main(), do: 42\n").expect("plain source should parse");
    assert_eq!(
        parsed, None,
        "ordinary fixtures2 sources should not need any contract header"
    );
}

#[test]
fn fixture_contract_parser_reads_metrics_edges_and_snapshot_directives() {
    let parsed = parse_fixture_contract(
        r#"#---
# purpose: closure call stays indirect
# root: main/0
# assert.metric.codegen.functions: 3
# assert.metric.codegen.instructions: 17
# assert.edge: main/0 | @66-71 | closure | main/0::lambda[@14-33]/1
# snapshot.call_edges: call_edges
#---
fn main(), do: 42
"#,
    )
    .expect("contract fixture should parse");

    assert_eq!(
        parsed,
        Some(FixtureContract {
            purpose: Some("closure call stays indirect".to_string()),
            root: Some(FixtureRoot {
                name: "main".to_string(),
                arity: 0,
            }),
            metric_assertions: vec![
                MetricAssertion {
                    name: "codegen.functions".to_string(),
                    expected: 3,
                },
                MetricAssertion {
                    name: "codegen.instructions".to_string(),
                    expected: 17,
                },
            ],
            edge_assertions: vec![EdgeAssertion {
                caller: "main/0".to_string(),
                callsite: "@66-71".to_string(),
                dispatch: "closure".to_string(),
                target: "main/0::lambda[@14-33]/1".to_string(),
            }],
            call_edge_snapshot: Some("call_edges".to_string()),
        }),
        "the contract block should carry the fixture's compiler-facing intent"
    );
}

#[test]
fn fixture_contract_parser_rejects_unknown_keys_and_duplicate_singletons() {
    let err = parse_fixture_contract(
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

    let err = parse_fixture_contract(
        r#"#---
# mystery: nope
#---
"#,
    )
    .expect_err("unknown key should be rejected");
    assert!(
        err.to_string().contains("unknown fixture contract key"),
        "contract grammar should be explicit, not open-ended: {err}",
    );
}

#[test]
fn fixture_contract_parser_requires_well_formed_root_and_edge_lines() {
    let err = parse_fixture_contract(
        r#"#---
# root: main
#---
"#,
    )
    .expect_err("root without arity should fail");
    assert!(
        err.to_string().contains("name/arity"),
        "root parsing should point authors at the exact shape we require: {err}",
    );

    let err = parse_fixture_contract(
        r#"#---
# assert.edge: main/0 | @12-20 | closure
#---
"#,
    )
    .expect_err("short edge assertion should fail");
    assert!(
        err.to_string().contains("caller | callsite | dispatch | target"),
        "edge assertions should keep one simple shape: {err}",
    );
}
