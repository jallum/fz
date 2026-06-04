use super::*;
use crate::types::Types;

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
