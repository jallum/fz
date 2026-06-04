use super::*;
use crate::types::{Ty, Types};
use std::collections::BTreeMap;

#[test]
fn builder_mints_stable_subject_and_arm_ids() {
    let mut builder = DispatchMatrixBuilder::new(Order::Source);
    let first_subject = builder.add_input_subject();
    let projected_subject = builder
        .add_projected_subject(first_subject, ProjectionKind::ListTail)
        .expect("projection source exists");
    let second_subject = builder.add_input_subject();
    let shared = builder.add_outcome(OutcomeMultiplicity::Shared);

    let first_arm = builder
        .add_arm(
            vec![RegionPredicate::new(first_subject, Region::List(ListRegion::Cons))],
            EdgeEvidence::empty(),
            shared,
        )
        .expect("first arm should be accepted");
    let second_arm = builder
        .add_arm(
            vec![RegionPredicate::new(second_subject, Region::Any)],
            EdgeEvidence::empty(),
            shared,
        )
        .expect("shared outcome can be reused");

    let matrix = builder.build().expect("source order is always valid");

    assert_eq!(first_subject, SubjectId(0));
    assert_eq!(projected_subject, SubjectId(1));
    assert_eq!(second_subject, SubjectId(2));
    assert_eq!(first_arm, ArmId(0));
    assert_eq!(second_arm, ArmId(1));
    assert_eq!(matrix.subject(first_subject).expect("subject exists").id, first_subject);
    assert!(matches!(
        matrix.subject(second_subject).expect("subject exists").source,
        SubjectSource::Input { ordinal: 1 }
    ));
    assert_eq!(matrix.arm(second_arm).expect("arm exists").outcome, shared);
}

#[test]
fn unique_outcome_cannot_be_routed_from_multiple_arms() {
    let mut builder = DispatchMatrixBuilder::new(Order::Source);
    let subject = builder.add_input_subject();
    let unique = builder.add_outcome(OutcomeMultiplicity::Unique);

    builder
        .add_arm(
            vec![RegionPredicate::new(
                subject,
                Region::Equal(ComparisonValue::Const(DispatchConst::Nil)),
            )],
            EdgeEvidence::empty(),
            unique,
        )
        .expect("first use of a unique outcome is valid");

    let err = builder
        .add_arm(
            vec![RegionPredicate::new(
                subject,
                Region::Equal(ComparisonValue::Const(DispatchConst::Nil)),
            )],
            EdgeEvidence::empty(),
            unique,
        )
        .expect_err("second use of a unique outcome must be rejected");

    assert_eq!(err, DispatchMatrixError::UniqueOutcomeReused(unique));
}

#[test]
fn edge_evidence_keeps_proofs_and_projections_branch_local() {
    let mut builder = DispatchMatrixBuilder::new(Order::Source);
    let list = builder.add_input_subject();
    let head = builder
        .add_projected_subject(list, ProjectionKind::ListHead)
        .expect("projection source exists");
    let outcome = builder.add_outcome(OutcomeMultiplicity::Unique);
    let predicate = RegionPredicate::new(list, Region::List(ListRegion::Cons));
    let evidence = EdgeEvidence {
        proofs: vec![Proof {
            predicate: predicate.clone(),
            sense: ProofSense::Holds,
        }],
        projections: vec![EdgeProjection {
            source: list,
            kind: ProjectionKind::ListHead,
            result: head,
        }],
    };

    let arm = builder
        .add_arm(vec![predicate], evidence.clone(), outcome)
        .expect("evidence references known subjects");
    let matrix = builder.build().expect("source order is valid");

    assert_eq!(matrix.arm(arm).expect("arm exists").evidence, evidence);
    assert!(matches!(
        matrix.subject(head).expect("projection subject exists").source,
        SubjectSource::Projection(SubjectProjection {
            source,
            kind: ProjectionKind::ListHead,
        }) if source == list
    ));
}

#[test]
fn map_key_presence_question_produces_value_or_absent_evidence() {
    let map = SubjectId(0);
    let value = SubjectId(1);
    let key = DispatchConst::AtomName("id".to_string());

    let question = RegionQuestion::map_key_present(map, key.clone(), value);

    assert_eq!(
        question.predicate,
        RegionPredicate::new(map, Region::MapKeyPresent { key: key.clone() })
    );
    assert_eq!(
        question.match_evidence.proofs,
        vec![Proof {
            predicate: question.predicate.clone(),
            sense: ProofSense::Holds,
        }]
    );
    assert_eq!(
        question.match_evidence.projections,
        vec![EdgeProjection {
            source: map,
            kind: ProjectionKind::MapValue { key },
            result: value,
        }]
    );
    assert_eq!(
        question.miss_evidence,
        EdgeEvidence::from_proof(question.predicate.clone(), ProofSense::DoesNotHold)
    );
}

#[test]
fn present_nil_map_value_is_value_equality_after_presence() {
    let map = SubjectId(0);
    let value = SubjectId(1);
    let presence = RegionQuestion::map_key_present(map, DispatchConst::Int(7), value);
    let nil_value = RegionQuestion::equality(value, ComparisonValue::Const(DispatchConst::Nil));

    assert!(matches!(
        presence.predicate.region,
        Region::MapKeyPresent {
            key: DispatchConst::Int(7)
        }
    ));
    assert_eq!(
        nil_value.predicate,
        RegionPredicate::new(value, Region::Equal(ComparisonValue::Const(DispatchConst::Nil)))
    );
}

#[test]
fn map_miss_is_not_source_level_vocabulary() {
    let dispatch_matrix_source = include_str!("mod.rs");
    assert!(!dispatch_matrix_source.contains("IsMatcherMapMiss"));
}

#[test]
fn list_shape_questions_preserve_empty_cons_and_non_list_distinctions() {
    let list = SubjectId(0);
    let head = SubjectId(1);
    let tail = SubjectId(2);

    let empty = RegionQuestion::list_empty(list);
    let cons = RegionQuestion::list_cons(list, head, tail);

    assert_eq!(
        empty.match_evidence,
        EdgeEvidence::from_proof(empty.predicate.clone(), ProofSense::Holds)
    );
    assert_eq!(
        empty.miss_evidence,
        EdgeEvidence::from_proof(empty.predicate.clone(), ProofSense::DoesNotHold)
    );
    assert_eq!(
        cons.match_evidence.projections,
        vec![
            EdgeProjection {
                source: list,
                kind: ProjectionKind::ListHead,
                result: head,
            },
            EdgeProjection {
                source: list,
                kind: ProjectionKind::ListTail,
                result: tail,
            },
        ]
    );
    assert_eq!(
        cons.miss_evidence,
        EdgeEvidence::from_proof(cons.predicate.clone(), ProofSense::DoesNotHold)
    );
}

#[test]
fn type_shape_and_equality_questions_share_graph_branch_shape() {
    let subject = SubjectId(0);
    let on_match = GraphNodeId(1);
    let on_miss = GraphNodeId(2);
    let mut types = crate::types::new();

    let questions = vec![
        RegionQuestion::type_region(subject, types.int()),
        RegionQuestion::list_empty(subject),
        RegionQuestion::equality(subject, ComparisonValue::Const(DispatchConst::Int(42))),
        RegionQuestion::equality(subject, ComparisonValue::Pinned(PinnedValueId(0))),
    ];

    for question in questions {
        let predicate = question.predicate.clone();
        let node = question.into_test_node(on_match, on_miss);
        let DispatchNode::Test {
            predicate: node_predicate,
            on_match: match_edge,
            on_miss: miss_edge,
        } = node
        else {
            panic!("region question should lower to one graph branch");
        };
        assert_eq!(node_predicate, predicate);
        assert_eq!(match_edge.target, on_match);
        assert_eq!(miss_edge.target, on_miss);
        assert_eq!(
            match_edge.evidence,
            EdgeEvidence::from_proof(predicate.clone(), ProofSense::Holds)
        );
        assert_eq!(
            miss_edge.evidence,
            EdgeEvidence::from_proof(predicate, ProofSense::DoesNotHold)
        );
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TestValue {
    Int(i64),
    Nil,
    EmptyList,
    Cons,
}

fn eval_graph(graph: &DispatchGraph, subject: SubjectId, value: TestValue) -> Option<OutcomeId> {
    let mut values = BTreeMap::new();
    values.insert(subject, value);
    eval_node(graph, graph.root, &values)
}

fn eval_node(graph: &DispatchGraph, node: GraphNodeId, values: &BTreeMap<SubjectId, TestValue>) -> Option<OutcomeId> {
    match graph.node(node).expect("node exists") {
        DispatchNode::Fail => None,
        DispatchNode::Outcome { outcome, .. } => Some(*outcome),
        DispatchNode::Test {
            predicate,
            on_match,
            on_miss,
        } => {
            let edge = if eval_predicate(predicate, values) {
                on_match
            } else {
                on_miss
            };
            eval_node(graph, edge.target, values)
        }
    }
}

fn eval_predicate(predicate: &RegionPredicate, values: &BTreeMap<SubjectId, TestValue>) -> bool {
    let Some(value) = values.get(&predicate.subject) else {
        return false;
    };
    match (&predicate.region, value) {
        (Region::Any, _) => true,
        (Region::Never, _) => false,
        (Region::Equal(ComparisonValue::Const(DispatchConst::Int(expected))), TestValue::Int(actual)) => {
            expected == actual
        }
        (Region::Equal(ComparisonValue::Const(DispatchConst::Nil)), TestValue::Nil) => true,
        (Region::Equal(ComparisonValue::Const(DispatchConst::EmptyList)), TestValue::EmptyList) => true,
        (Region::List(ListRegion::Empty), TestValue::EmptyList) => true,
        (Region::List(ListRegion::Cons), TestValue::Cons) => true,
        _ => false,
    }
}

fn matrix_with_subject() -> (DispatchMatrixBuilder, SubjectId) {
    let mut builder = DispatchMatrixBuilder::new(Order::Source);
    let subject = builder.add_input_subject();
    (builder, subject)
}

#[test]
fn compile_source_order_uses_first_matching_arm() {
    let (mut builder, subject) = matrix_with_subject();
    let one = builder.add_outcome(OutcomeMultiplicity::Unique);
    let fallback = builder.add_outcome(OutcomeMultiplicity::Unique);

    builder
        .add_arm_questions(
            vec![RegionQuestion::equality(
                subject,
                ComparisonValue::Const(DispatchConst::Int(1)),
            )],
            EdgeEvidence::empty(),
            one,
        )
        .expect("specific arm");
    builder
        .add_arm(Vec::new(), EdgeEvidence::empty(), fallback)
        .expect("source fallback arm");
    let matrix = builder.build().expect("matrix");

    let compiled = compile_dispatch_matrix(&matrix, DispatchCompileOptions::closed()).expect("compile");

    assert_eq!(eval_graph(&compiled.graph, subject, TestValue::Int(1)), Some(one));
    assert_eq!(eval_graph(&compiled.graph, subject, TestValue::Int(2)), Some(fallback));
}

#[test]
fn compile_orthogonal_arms_in_deterministic_source_order() {
    let (mut builder, subject) = matrix_with_subject();
    let two = builder.add_outcome(OutcomeMultiplicity::Unique);
    let one = builder.add_outcome(OutcomeMultiplicity::Unique);

    builder
        .add_arm_questions(
            vec![RegionQuestion::equality(
                subject,
                ComparisonValue::Const(DispatchConst::Int(2)),
            )],
            EdgeEvidence::empty(),
            two,
        )
        .expect("first orthogonal arm");
    builder
        .add_arm_questions(
            vec![RegionQuestion::equality(
                subject,
                ComparisonValue::Const(DispatchConst::Int(1)),
            )],
            EdgeEvidence::empty(),
            one,
        )
        .expect("second orthogonal arm");
    let matrix = builder.build().expect("matrix");

    let compiled = compile_dispatch_matrix(&matrix, DispatchCompileOptions::closed()).expect("compile");
    let Some(DispatchNode::Test { predicate, .. }) = compiled.graph.node(compiled.graph.root) else {
        panic!("expected root test");
    };

    assert_eq!(
        predicate.region,
        Region::Equal(ComparisonValue::Const(DispatchConst::Int(2)))
    );
    assert_eq!(eval_graph(&compiled.graph, subject, TestValue::Int(2)), Some(two));
    assert_eq!(eval_graph(&compiled.graph, subject, TestValue::Int(1)), Some(one));
}

#[test]
fn compile_shares_consecutive_common_prefix_tests() {
    let mut builder = DispatchMatrixBuilder::new(Order::Source);
    let list = builder.add_input_subject();
    let head = builder
        .add_projected_subject(list, ProjectionKind::ListHead)
        .expect("head subject");
    let tail = builder
        .add_projected_subject(list, ProjectionKind::ListTail)
        .expect("tail subject");
    let first = builder.add_outcome(OutcomeMultiplicity::Unique);
    let second = builder.add_outcome(OutcomeMultiplicity::Unique);
    let cons = RegionQuestion::list_cons(list, head, tail);

    builder
        .add_arm_questions(
            vec![
                cons.clone(),
                RegionQuestion::equality(head, ComparisonValue::Const(DispatchConst::Int(1))),
            ],
            EdgeEvidence::empty(),
            first,
        )
        .expect("first cons arm");
    builder
        .add_arm_questions(
            vec![
                cons.clone(),
                RegionQuestion::equality(head, ComparisonValue::Const(DispatchConst::Int(2))),
            ],
            EdgeEvidence::empty(),
            second,
        )
        .expect("second cons arm");
    let matrix = builder.build().expect("matrix");

    let compiled = compile_dispatch_matrix(&matrix, DispatchCompileOptions::closed()).expect("compile");
    let Some(DispatchNode::Test { predicate, .. }) = compiled.graph.node(compiled.graph.root) else {
        panic!("expected shared root test");
    };

    assert_eq!(*predicate, cons.predicate);
    assert_eq!(compiled.stats.shared_prefix_tests, 1);
    assert_eq!(compiled.stats.test_nodes, 3);
}

#[test]
fn compile_open_residual_uses_fallback_and_closed_residual_fails() {
    let (mut builder, subject) = matrix_with_subject();
    let one = builder.add_outcome(OutcomeMultiplicity::Unique);
    let fallback = builder.add_outcome(OutcomeMultiplicity::Unique);
    builder
        .add_arm_questions(
            vec![RegionQuestion::equality(
                subject,
                ComparisonValue::Const(DispatchConst::Int(1)),
            )],
            EdgeEvidence::empty(),
            one,
        )
        .expect("specific arm");
    let matrix = builder.build().expect("matrix");

    let closed = compile_dispatch_matrix(&matrix, DispatchCompileOptions::closed()).expect("closed compile");
    let open = compile_dispatch_matrix(&matrix, DispatchCompileOptions::open(fallback)).expect("open compile");

    assert_eq!(eval_graph(&closed.graph, subject, TestValue::Int(2)), None);
    assert_eq!(eval_graph(&open.graph, subject, TestValue::Int(2)), Some(fallback));
    assert_eq!(closed.stats.fail_nodes, 1);
    assert_eq!(closed.stats.fallback_nodes, 0);
    assert_eq!(open.stats.fail_nodes, 0);
    assert_eq!(open.stats.fallback_nodes, 1);
}

#[test]
fn compile_places_projection_only_on_proven_edge() {
    let mut builder = DispatchMatrixBuilder::new(Order::Source);
    let map = builder.add_input_subject();
    let value = builder
        .add_projected_subject(
            map,
            ProjectionKind::MapValue {
                key: DispatchConst::AtomName("id".to_string()),
            },
        )
        .expect("map value subject");
    let matched = builder.add_outcome(OutcomeMultiplicity::Unique);
    let key = DispatchConst::AtomName("id".to_string());

    builder
        .add_arm_questions(
            vec![
                RegionQuestion::map_key_present(map, key.clone(), value),
                RegionQuestion::equality(value, ComparisonValue::Const(DispatchConst::Nil)),
            ],
            EdgeEvidence::empty(),
            matched,
        )
        .expect("map presence arm");
    let matrix = builder.build().expect("matrix");

    let compiled = compile_dispatch_matrix(&matrix, DispatchCompileOptions::closed()).expect("compile");
    let Some(DispatchNode::Test {
        predicate,
        on_match,
        on_miss,
    }) = compiled.graph.node(compiled.graph.root)
    else {
        panic!("expected map presence root");
    };

    assert_eq!(predicate.region, Region::MapKeyPresent { key: key.clone() });
    assert_eq!(
        on_match.evidence.projections,
        vec![EdgeProjection {
            source: map,
            kind: ProjectionKind::MapValue { key },
            result: value,
        }]
    );
    assert!(on_miss.evidence.projections.is_empty());
    assert!(matches!(
        compiled.graph.node(on_match.target),
        Some(DispatchNode::Test {
            predicate: RegionPredicate {
                subject,
                region: Region::Equal(ComparisonValue::Const(DispatchConst::Nil)),
            },
            ..
        }) if *subject == value
    ));
}

fn type_arm(arm: u32, ty: Ty, outcome: u32) -> TypeRegionArm {
    TypeRegionArm {
        arm: ArmId(arm),
        subject: SubjectId(0),
        ty,
        outcome: OutcomeId(outcome),
    }
}

#[test]
fn type_region_relation_classifies_scalars_lists_maps_range_like_any_and_empty_overlap() {
    let mut types = crate::types::new();
    let int = types.int();
    let float = types.float();
    let any = types.any();
    let list_int = types.list(int.clone());
    let list_any = types.list(any.clone());
    let map = types.map_top();
    let range = types.opaque_of("impl-target::Range");

    assert_eq!(
        type_region_relation(&types, &int, &any),
        TypeRegionRelation::LeftMoreSpecific
    );
    assert_eq!(
        type_region_relation(&types, &any, &int),
        TypeRegionRelation::RightMoreSpecific
    );
    assert_eq!(type_region_relation(&types, &int, &float), TypeRegionRelation::Disjoint);
    assert_eq!(
        type_region_relation(&types, &list_int, &list_any),
        TypeRegionRelation::LeftMoreSpecific
    );
    assert_eq!(
        type_region_relation(&types, &map, &any),
        TypeRegionRelation::LeftMoreSpecific
    );
    assert_eq!(
        type_region_relation(&types, &range, &any),
        TypeRegionRelation::LeftMoreSpecific
    );
    assert_eq!(type_region_relation(&types, &range, &int), TypeRegionRelation::Disjoint);
}

#[test]
fn type_region_analysis_sorts_more_specific_before_less_specific() {
    let mut types = crate::types::new();
    let any = types.any();
    let int = types.int();
    let list_any = types.list(any.clone());
    let arms = vec![type_arm(0, any, 0), type_arm(1, int, 1), type_arm(2, list_any, 2)];

    let analysis = analyze_type_region_arms(&mut types, &arms, EqualTypeRegionPolicy::DuplicateCoverage);

    assert_eq!(analysis.ordered_arms, vec![ArmId(1), ArmId(2), ArmId(0)]);
    assert!(analysis.diagnostics.is_empty());
}

#[test]
fn type_region_analysis_reports_equal_regions_by_policy() {
    let mut types = crate::types::new();
    let int = types.int();
    let duplicate_arms = vec![type_arm(0, int.clone(), 0), type_arm(1, int, 1)];

    let duplicate = analyze_type_region_arms(&mut types, &duplicate_arms, EqualTypeRegionPolicy::DuplicateCoverage);
    let ambiguous = analyze_type_region_arms(&mut types, &duplicate_arms, EqualTypeRegionPolicy::Ambiguous);

    assert_eq!(
        duplicate.diagnostics,
        vec![TypeRegionDiagnostic {
            kind: TypeRegionDiagnosticKind::DuplicateCoverage,
            left: ArmId(0),
            right: ArmId(1),
        }]
    );
    assert_eq!(
        ambiguous.diagnostics,
        vec![TypeRegionDiagnostic {
            kind: TypeRegionDiagnosticKind::AmbiguousEqualRegions,
            left: ArmId(0),
            right: ArmId(1),
        }]
    );
}

#[test]
fn type_region_analysis_recognizes_orthogonal_and_ambiguous_overlaps() {
    let mut types = crate::types::new();
    let int = types.int();
    let float = types.float();
    let list_int = types.list(int.clone());
    let list_float = types.list(float.clone());
    let orthogonal = vec![type_arm(0, int, 0), type_arm(1, float, 1)];
    let ambiguous_overlap = vec![type_arm(2, list_int, 2), type_arm(3, list_float, 3)];

    let orthogonal_analysis =
        analyze_type_region_arms(&mut types, &orthogonal, EqualTypeRegionPolicy::DuplicateCoverage);
    let ambiguous_analysis =
        analyze_type_region_arms(&mut types, &ambiguous_overlap, EqualTypeRegionPolicy::DuplicateCoverage);

    assert_eq!(
        orthogonal_analysis.pairs[0].relation,
        TypeRegionRelation::Disjoint,
        "disjoint arms are orthogonal and need no priority"
    );
    assert!(orthogonal_analysis.diagnostics.is_empty());
    assert_eq!(
        ambiguous_analysis.diagnostics,
        vec![TypeRegionDiagnostic {
            kind: TypeRegionDiagnosticKind::AmbiguousOverlap,
            left: ArmId(2),
            right: ArmId(3),
        }]
    );
}

#[test]
fn type_coverage_distinguishes_closed_union_from_open_residual() {
    let mut types = crate::types::new();
    let int = types.int();
    let any = types.any();
    let list_any = types.list(any.clone());
    let domain = types.union(int.clone(), list_any.clone());
    let arms = vec![type_arm(0, int, 0), type_arm(1, list_any, 1)];

    let closed = analyze_type_coverage(&mut types, domain, &arms);
    let open = analyze_type_coverage(&mut types, any, &arms);

    assert_eq!(closed.status, TypeCoverageStatus::Closed);
    assert!(types.is_empty(&closed.residual));
    assert_eq!(open.status, TypeCoverageStatus::Open);
    assert!(!types.is_empty(&open.residual));
}

#[test]
fn compile_specificity_order_uses_type_analysis() {
    let mut types = crate::types::new();
    let any = types.any();
    let int = types.int();
    let mut builder = DispatchMatrixBuilder::new(Order::Specificity);
    let subject = builder.add_input_subject();
    let broad = builder.add_outcome(OutcomeMultiplicity::Unique);
    let narrow = builder.add_outcome(OutcomeMultiplicity::Unique);

    builder
        .add_arm_questions(
            vec![RegionQuestion::type_region(subject, any)],
            EdgeEvidence::empty(),
            broad,
        )
        .expect("broad arm");
    builder
        .add_arm_questions(
            vec![RegionQuestion::type_region(subject, int.clone())],
            EdgeEvidence::empty(),
            narrow,
        )
        .expect("narrow arm");
    let matrix = builder.build().expect("matrix");

    let compiled = compile_dispatch_matrix_with_type_order(
        &mut types,
        &matrix,
        DispatchCompileOptions::closed(),
        EqualTypeRegionPolicy::DuplicateCoverage,
    )
    .expect("specificity compile");
    let Some(DispatchNode::Test { predicate, .. }) = compiled.graph.node(compiled.graph.root) else {
        panic!("expected type test root");
    };

    assert_eq!(predicate.region, Region::Type(int));
}

#[test]
fn graph_builder_preserves_node_identity_and_validates_edges() {
    let mut builder = DispatchGraphBuilder::new();
    let fail = builder.add_node(DispatchNode::Fail);
    let out = builder.add_node(DispatchNode::Outcome {
        outcome: OutcomeId(0),
        evidence: EdgeEvidence::empty(),
    });
    let test = builder.add_node(DispatchNode::Test {
        predicate: RegionPredicate::new(SubjectId(0), Region::Any),
        on_match: DispatchEdge::new(out),
        on_miss: DispatchEdge::new(fail),
    });

    let graph = builder.build(test).expect("all node edges are valid");

    assert_eq!(fail, GraphNodeId(0));
    assert_eq!(out, GraphNodeId(1));
    assert_eq!(test, GraphNodeId(2));
    assert!(matches!(graph.node(graph.root), Some(DispatchNode::Test { .. })));
}

#[test]
fn graph_builder_rejects_unknown_root_or_edge_node() {
    let mut unknown_root = DispatchGraphBuilder::new();
    unknown_root.add_node(DispatchNode::Fail);
    assert_eq!(
        unknown_root.build(GraphNodeId(9)).expect_err("root must exist"),
        DispatchGraphError::UnknownNode(GraphNodeId(9))
    );

    let mut unknown_edge = DispatchGraphBuilder::new();
    let fail = unknown_edge.add_node(DispatchNode::Fail);
    let test = unknown_edge.add_node(DispatchNode::Test {
        predicate: RegionPredicate::new(SubjectId(0), Region::Any),
        on_match: DispatchEdge::new(GraphNodeId(42)),
        on_miss: DispatchEdge::new(fail),
    });
    assert_eq!(
        unknown_edge.build(test).expect_err("edge target must exist"),
        DispatchGraphError::UnknownNode(GraphNodeId(42))
    );
}
