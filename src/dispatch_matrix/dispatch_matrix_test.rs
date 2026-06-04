use super::*;

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
            vec![RegionPredicate::new(subject, Region::Const(DispatchConst::Nil))],
            EdgeEvidence::empty(),
            unique,
        )
        .expect("first use of a unique outcome is valid");

    let err = builder
        .add_arm(
            vec![RegionPredicate::new(subject, Region::Any)],
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
