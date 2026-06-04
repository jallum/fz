//! Side-by-side model for region-based dispatch.
//!
//! fz-v19.1 deliberately adds only the data model. Later tickets add producers
//! and graph compilation; until then these public-in-crate types have no
//! production callers.
#![allow(dead_code)]

use crate::types::Ty;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct SubjectId(pub(crate) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct ArmId(pub(crate) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct OutcomeId(pub(crate) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct GraphNodeId(pub(crate) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct GuardId(pub(crate) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct PinnedValueId(pub(crate) u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DispatchMatrix {
    pub(crate) subjects: Vec<Subject>,
    pub(crate) outcomes: Vec<Outcome>,
    pub(crate) arms: Vec<DispatchArm>,
    pub(crate) order: Order,
}

impl DispatchMatrix {
    pub(crate) fn subject(&self, id: SubjectId) -> Option<&Subject> {
        self.subjects.get(id.0 as usize)
    }

    pub(crate) fn outcome(&self, id: OutcomeId) -> Option<&Outcome> {
        self.outcomes.get(id.0 as usize)
    }

    pub(crate) fn arm(&self, id: ArmId) -> Option<&DispatchArm> {
        self.arms.get(id.0 as usize)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Subject {
    pub(crate) id: SubjectId,
    pub(crate) source: SubjectSource,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SubjectSource {
    Input { ordinal: u32 },
    Projection(SubjectProjection),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SubjectProjection {
    pub(crate) source: SubjectId,
    pub(crate) kind: ProjectionKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ProjectionKind {
    TupleField(u32),
    ListHead,
    ListTail,
    MapValue { key: DispatchConst },
    BitstringField(u32),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DispatchArm {
    pub(crate) id: ArmId,
    pub(crate) questions: Vec<RegionQuestion>,
    pub(crate) evidence: EdgeEvidence,
    pub(crate) outcome: OutcomeId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RegionPredicate {
    pub(crate) subject: SubjectId,
    pub(crate) region: Region,
}

impl RegionPredicate {
    pub(crate) fn new(subject: SubjectId, region: Region) -> Self {
        Self { subject, region }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Region {
    Any,
    Never,
    Type(Ty),
    Equal(ComparisonValue),
    TupleArity(u32),
    List(ListRegion),
    MapKind,
    MapKeyPresent { key: DispatchConst },
    Bitstring(BitstringShape),
    Guard(GuardId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ComparisonValue {
    Const(DispatchConst),
    Pinned(PinnedValueId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ListRegion {
    Empty,
    Cons,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BitstringShape {
    pub(crate) fields: Vec<BitstringFieldShape>,
    pub(crate) require_done: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BitstringFieldShape {
    pub(crate) kind: BitstringFieldKind,
    pub(crate) size: Option<BitstringFieldSize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum BitstringFieldKind {
    Integer,
    Float,
    Binary,
    Bits,
    Utf8,
    Utf16,
    Utf32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum BitstringFieldSize {
    Literal(u32),
    Binding(SubjectId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum DispatchConst {
    Int(i64),
    FloatBits(u64),
    AtomName(String),
    Bool(bool),
    Nil,
    EmptyList,
    Utf8Binary(Vec<u8>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Order {
    /// Source-pattern semantics: first matching arm wins.
    Source,
    /// Type-dispatch semantics: more-specific regions win; incomparable
    /// overlaps are diagnosed by later analysis.
    Specificity,
    /// A fully materialized order. Useful for tests and future graph snapshots.
    Explicit(Vec<ArmId>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Outcome {
    pub(crate) id: OutcomeId,
    pub(crate) multiplicity: OutcomeMultiplicity,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OutcomeMultiplicity {
    /// At most one arm may route to this outcome.
    Unique,
    /// Multiple arms may share this outcome.
    Shared,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct EdgeEvidence {
    pub(crate) proofs: Vec<Proof>,
    pub(crate) projections: Vec<EdgeProjection>,
}

impl EdgeEvidence {
    pub(crate) fn empty() -> Self {
        Self::default()
    }

    pub(crate) fn from_proof(predicate: RegionPredicate, sense: ProofSense) -> Self {
        Self {
            proofs: vec![Proof { predicate, sense }],
            projections: Vec::new(),
        }
    }

    pub(crate) fn with_projection(mut self, projection: EdgeProjection) -> Self {
        self.projections.push(projection);
        self
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Proof {
    pub(crate) predicate: RegionPredicate,
    pub(crate) sense: ProofSense,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProofSense {
    Holds,
    DoesNotHold,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EdgeProjection {
    pub(crate) source: SubjectId,
    pub(crate) kind: ProjectionKind,
    pub(crate) result: SubjectId,
}

/// One normalized branch question over one subject.
///
/// This is the DispatchMatrix-level vocabulary. It names the semantic region
/// being tested and the evidence each branch produces. Existing backend
/// primitives are lowering choices for these questions, not additional semantic
/// variants in this model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RegionQuestion {
    pub(crate) predicate: RegionPredicate,
    pub(crate) match_evidence: EdgeEvidence,
    pub(crate) miss_evidence: EdgeEvidence,
}

impl RegionQuestion {
    pub(crate) fn new(predicate: RegionPredicate) -> Self {
        Self {
            match_evidence: EdgeEvidence::from_proof(predicate.clone(), ProofSense::Holds),
            miss_evidence: EdgeEvidence::from_proof(predicate.clone(), ProofSense::DoesNotHold),
            predicate,
        }
    }

    pub(crate) fn type_region(subject: SubjectId, ty: Ty) -> Self {
        Self::new(RegionPredicate::new(subject, Region::Type(ty)))
    }

    pub(crate) fn equality(subject: SubjectId, value: ComparisonValue) -> Self {
        Self::new(RegionPredicate::new(subject, Region::Equal(value)))
    }

    pub(crate) fn list_empty(subject: SubjectId) -> Self {
        Self::new(RegionPredicate::new(subject, Region::List(ListRegion::Empty)))
    }

    pub(crate) fn list_cons(subject: SubjectId, head: SubjectId, tail: SubjectId) -> Self {
        let predicate = RegionPredicate::new(subject, Region::List(ListRegion::Cons));
        Self {
            match_evidence: EdgeEvidence::from_proof(predicate.clone(), ProofSense::Holds)
                .with_projection(EdgeProjection {
                    source: subject,
                    kind: ProjectionKind::ListHead,
                    result: head,
                })
                .with_projection(EdgeProjection {
                    source: subject,
                    kind: ProjectionKind::ListTail,
                    result: tail,
                }),
            miss_evidence: EdgeEvidence::from_proof(predicate.clone(), ProofSense::DoesNotHold),
            predicate,
        }
    }

    pub(crate) fn map_key_present(subject: SubjectId, key: DispatchConst, value: SubjectId) -> Self {
        let predicate = RegionPredicate::new(subject, Region::MapKeyPresent { key: key.clone() });
        Self {
            match_evidence: EdgeEvidence::from_proof(predicate.clone(), ProofSense::Holds).with_projection(
                EdgeProjection {
                    source: subject,
                    kind: ProjectionKind::MapValue { key },
                    result: value,
                },
            ),
            miss_evidence: EdgeEvidence::from_proof(predicate.clone(), ProofSense::DoesNotHold),
            predicate,
        }
    }

    pub(crate) fn into_test_node(self, on_match: GraphNodeId, on_miss: GraphNodeId) -> DispatchNode {
        DispatchNode::Test {
            predicate: self.predicate,
            on_match: DispatchEdge::with_evidence(on_match, self.match_evidence),
            on_miss: DispatchEdge::with_evidence(on_miss, self.miss_evidence),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DispatchGraph {
    pub(crate) nodes: Vec<DispatchNode>,
    pub(crate) root: GraphNodeId,
}

impl DispatchGraph {
    pub(crate) fn node(&self, id: GraphNodeId) -> Option<&DispatchNode> {
        self.nodes.get(id.0 as usize)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DispatchNode {
    Fail,
    Outcome {
        outcome: OutcomeId,
        evidence: EdgeEvidence,
    },
    Test {
        predicate: RegionPredicate,
        on_match: DispatchEdge,
        on_miss: DispatchEdge,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DispatchEdge {
    pub(crate) target: GraphNodeId,
    pub(crate) evidence: EdgeEvidence,
}

impl DispatchEdge {
    pub(crate) fn new(target: GraphNodeId) -> Self {
        Self {
            target,
            evidence: EdgeEvidence::empty(),
        }
    }

    pub(crate) fn with_evidence(target: GraphNodeId, evidence: EdgeEvidence) -> Self {
        Self { target, evidence }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DispatchMatrixError {
    UnknownSubject(SubjectId),
    UnknownOutcome(OutcomeId),
    UniqueOutcomeReused(OutcomeId),
    UnknownArmInOrder(ArmId),
    DuplicateArmInOrder(ArmId),
    IncompleteExplicitOrder { expected: usize, actual: usize },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DispatchCompileError {
    UnknownOutcome(OutcomeId),
    UnknownArm(ArmId),
    SpecificityOrderRequiresTypeAnalysis,
    InvalidGraph(DispatchGraphError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ResidualCoverage {
    Closed,
    Open { fallback: OutcomeId },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct DispatchCompileOptions {
    pub(crate) residual: ResidualCoverage,
}

impl DispatchCompileOptions {
    pub(crate) fn closed() -> Self {
        Self {
            residual: ResidualCoverage::Closed,
        }
    }

    pub(crate) fn open(fallback: OutcomeId) -> Self {
        Self {
            residual: ResidualCoverage::Open { fallback },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct DispatchCompileStats {
    pub(crate) arms: usize,
    pub(crate) test_nodes: usize,
    pub(crate) outcome_nodes: usize,
    pub(crate) fail_nodes: usize,
    pub(crate) fallback_nodes: usize,
    pub(crate) shared_prefix_tests: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CompiledDispatchGraph {
    pub(crate) graph: DispatchGraph,
    pub(crate) stats: DispatchCompileStats,
}

#[derive(Debug, Clone)]
struct ArmCompileState<'a> {
    arm: &'a DispatchArm,
    questions: Vec<RegionQuestion>,
}

pub(crate) fn compile_dispatch_matrix(
    matrix: &DispatchMatrix,
    options: DispatchCompileOptions,
) -> Result<CompiledDispatchGraph, DispatchCompileError> {
    let ordered_arms = ordered_arms(matrix)?;
    let mut stats = DispatchCompileStats {
        arms: ordered_arms.len(),
        ..DispatchCompileStats::default()
    };
    let mut builder = DispatchGraphBuilder::new();
    let fallback = fallback_node(matrix, options, &mut builder, &mut stats)?;
    let states = ordered_arms
        .into_iter()
        .map(|arm| ArmCompileState {
            arm,
            questions: arm.questions.clone(),
        })
        .collect::<Vec<_>>();
    let root = compile_arm_sequence(&states, fallback, &mut builder, &mut stats);
    let graph = builder.build(root).map_err(DispatchCompileError::InvalidGraph)?;
    Ok(CompiledDispatchGraph { graph, stats })
}

fn fallback_node(
    matrix: &DispatchMatrix,
    options: DispatchCompileOptions,
    builder: &mut DispatchGraphBuilder,
    stats: &mut DispatchCompileStats,
) -> Result<GraphNodeId, DispatchCompileError> {
    match options.residual {
        ResidualCoverage::Closed => {
            stats.fail_nodes += 1;
            Ok(builder.add_node(DispatchNode::Fail))
        }
        ResidualCoverage::Open { fallback } => {
            matrix
                .outcome(fallback)
                .ok_or(DispatchCompileError::UnknownOutcome(fallback))?;
            stats.outcome_nodes += 1;
            stats.fallback_nodes += 1;
            Ok(builder.add_node(DispatchNode::Outcome {
                outcome: fallback,
                evidence: EdgeEvidence::empty(),
            }))
        }
    }
}

fn ordered_arms(matrix: &DispatchMatrix) -> Result<Vec<&DispatchArm>, DispatchCompileError> {
    match &matrix.order {
        Order::Source => Ok(matrix.arms.iter().collect()),
        Order::Explicit(order) => {
            let mut out = Vec::with_capacity(order.len());
            for &id in order {
                let Some(arm) = matrix.arm(id) else {
                    return Err(DispatchCompileError::UnknownArm(id));
                };
                out.push(arm);
            }
            Ok(out)
        }
        Order::Specificity => Err(DispatchCompileError::SpecificityOrderRequiresTypeAnalysis),
    }
}

fn compile_arm_sequence(
    arms: &[ArmCompileState<'_>],
    fallback: GraphNodeId,
    builder: &mut DispatchGraphBuilder,
    stats: &mut DispatchCompileStats,
) -> GraphNodeId {
    let Some(first) = arms.first() else {
        return fallback;
    };
    let Some(first_question) = first.questions.first().cloned() else {
        return outcome_node(first.arm, builder, stats);
    };

    let shared_count = arms
        .iter()
        .take_while(|arm| arm.questions.first() == Some(&first_question))
        .count();
    if shared_count > 1 {
        stats.shared_prefix_tests += 1;
        let after_shared = compile_arm_sequence(&arms[shared_count..], fallback, builder, stats);
        let stripped = arms[..shared_count]
            .iter()
            .map(|arm| ArmCompileState {
                arm: arm.arm,
                questions: arm.questions[1..].to_vec(),
            })
            .collect::<Vec<_>>();
        let on_match = compile_arm_sequence(&stripped, after_shared, builder, stats);
        return test_node(first_question, on_match, after_shared, builder, stats);
    }

    let on_miss = compile_arm_sequence(&arms[1..], fallback, builder, stats);
    compile_single_arm(first, on_miss, builder, stats)
}

fn compile_single_arm(
    arm: &ArmCompileState<'_>,
    on_miss: GraphNodeId,
    builder: &mut DispatchGraphBuilder,
    stats: &mut DispatchCompileStats,
) -> GraphNodeId {
    let mut current = outcome_node(arm.arm, builder, stats);
    for question in arm.questions.iter().rev() {
        current = test_node(question.clone(), current, on_miss, builder, stats);
    }
    current
}

fn outcome_node(
    arm: &DispatchArm,
    builder: &mut DispatchGraphBuilder,
    stats: &mut DispatchCompileStats,
) -> GraphNodeId {
    stats.outcome_nodes += 1;
    builder.add_node(DispatchNode::Outcome {
        outcome: arm.outcome,
        evidence: arm.evidence.clone(),
    })
}

fn test_node(
    question: RegionQuestion,
    on_match: GraphNodeId,
    on_miss: GraphNodeId,
    builder: &mut DispatchGraphBuilder,
    stats: &mut DispatchCompileStats,
) -> GraphNodeId {
    stats.test_nodes += 1;
    builder.add_node(question.into_test_node(on_match, on_miss))
}

pub(crate) struct DispatchMatrixBuilder {
    order: Order,
    subjects: Vec<Subject>,
    input_count: u32,
    outcomes: Vec<Outcome>,
    arms: Vec<DispatchArm>,
    outcome_uses: BTreeMap<OutcomeId, usize>,
}

impl DispatchMatrixBuilder {
    pub(crate) fn new(order: Order) -> Self {
        Self {
            order,
            subjects: Vec::new(),
            input_count: 0,
            outcomes: Vec::new(),
            arms: Vec::new(),
            outcome_uses: BTreeMap::new(),
        }
    }

    pub(crate) fn add_input_subject(&mut self) -> SubjectId {
        let id = SubjectId(self.subjects.len() as u32);
        let ordinal = self.input_count;
        self.input_count += 1;
        self.subjects.push(Subject {
            id,
            source: SubjectSource::Input { ordinal },
        });
        id
    }

    pub(crate) fn add_projected_subject(
        &mut self,
        source: SubjectId,
        kind: ProjectionKind,
    ) -> Result<SubjectId, DispatchMatrixError> {
        self.ensure_subject(source)?;
        let id = SubjectId(self.subjects.len() as u32);
        self.subjects.push(Subject {
            id,
            source: SubjectSource::Projection(SubjectProjection { source, kind }),
        });
        Ok(id)
    }

    pub(crate) fn add_outcome(&mut self, multiplicity: OutcomeMultiplicity) -> OutcomeId {
        let id = OutcomeId(self.outcomes.len() as u32);
        self.outcomes.push(Outcome { id, multiplicity });
        id
    }

    pub(crate) fn add_arm(
        &mut self,
        predicates: Vec<RegionPredicate>,
        evidence: EdgeEvidence,
        outcome: OutcomeId,
    ) -> Result<ArmId, DispatchMatrixError> {
        let questions = predicates.into_iter().map(RegionQuestion::new).collect();
        self.add_arm_questions(questions, evidence, outcome)
    }

    pub(crate) fn add_arm_questions(
        &mut self,
        questions: Vec<RegionQuestion>,
        evidence: EdgeEvidence,
        outcome: OutcomeId,
    ) -> Result<ArmId, DispatchMatrixError> {
        for question in &questions {
            self.ensure_question_subjects(question)?;
        }
        self.ensure_evidence_subjects(&evidence)?;
        let outcome_id = outcome;
        let outcome_multiplicity = self.ensure_outcome(outcome_id)?.multiplicity;
        if outcome_multiplicity == OutcomeMultiplicity::Unique
            && self.outcome_uses.get(&outcome_id).copied().unwrap_or(0) > 0
        {
            return Err(DispatchMatrixError::UniqueOutcomeReused(outcome_id));
        }

        let id = ArmId(self.arms.len() as u32);
        self.arms.push(DispatchArm {
            id,
            questions,
            evidence,
            outcome: outcome_id,
        });
        *self.outcome_uses.entry(outcome_id).or_default() += 1;
        Ok(id)
    }

    pub(crate) fn build(self) -> Result<DispatchMatrix, DispatchMatrixError> {
        self.validate_order()?;
        Ok(DispatchMatrix {
            subjects: self.subjects,
            outcomes: self.outcomes,
            arms: self.arms,
            order: self.order,
        })
    }

    fn validate_order(&self) -> Result<(), DispatchMatrixError> {
        let Order::Explicit(order) = &self.order else {
            return Ok(());
        };
        let known: BTreeSet<_> = self.arms.iter().map(|arm| arm.id).collect();
        let mut seen = BTreeSet::new();
        for &arm in order {
            if !known.contains(&arm) {
                return Err(DispatchMatrixError::UnknownArmInOrder(arm));
            }
            if !seen.insert(arm) {
                return Err(DispatchMatrixError::DuplicateArmInOrder(arm));
            }
        }
        if seen.len() != known.len() {
            return Err(DispatchMatrixError::IncompleteExplicitOrder {
                expected: known.len(),
                actual: seen.len(),
            });
        }
        Ok(())
    }

    fn ensure_subject(&self, id: SubjectId) -> Result<(), DispatchMatrixError> {
        self.subjects
            .get(id.0 as usize)
            .map(|_| ())
            .ok_or(DispatchMatrixError::UnknownSubject(id))
    }

    fn ensure_outcome(&self, id: OutcomeId) -> Result<&Outcome, DispatchMatrixError> {
        self.outcomes
            .get(id.0 as usize)
            .ok_or(DispatchMatrixError::UnknownOutcome(id))
    }

    fn ensure_evidence_subjects(&self, evidence: &EdgeEvidence) -> Result<(), DispatchMatrixError> {
        for proof in &evidence.proofs {
            self.ensure_subject(proof.predicate.subject)?;
        }
        for projection in &evidence.projections {
            self.ensure_subject(projection.source)?;
            self.ensure_subject(projection.result)?;
        }
        Ok(())
    }

    fn ensure_question_subjects(&self, question: &RegionQuestion) -> Result<(), DispatchMatrixError> {
        self.ensure_subject(question.predicate.subject)?;
        self.ensure_evidence_subjects(&question.match_evidence)?;
        self.ensure_evidence_subjects(&question.miss_evidence)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DispatchGraphError {
    UnknownNode(GraphNodeId),
}

pub(crate) struct DispatchGraphBuilder {
    nodes: Vec<DispatchNode>,
}

impl DispatchGraphBuilder {
    pub(crate) fn new() -> Self {
        Self { nodes: Vec::new() }
    }

    pub(crate) fn add_node(&mut self, node: DispatchNode) -> GraphNodeId {
        let id = GraphNodeId(self.nodes.len() as u32);
        self.nodes.push(node);
        id
    }

    pub(crate) fn build(self, root: GraphNodeId) -> Result<DispatchGraph, DispatchGraphError> {
        self.ensure_node(root)?;
        for node in &self.nodes {
            if let DispatchNode::Test { on_match, on_miss, .. } = node {
                self.ensure_node(on_match.target)?;
                self.ensure_node(on_miss.target)?;
            }
        }
        Ok(DispatchGraph {
            nodes: self.nodes,
            root,
        })
    }

    fn ensure_node(&self, id: GraphNodeId) -> Result<(), DispatchGraphError> {
        self.nodes
            .get(id.0 as usize)
            .map(|_| ())
            .ok_or(DispatchGraphError::UnknownNode(id))
    }
}

#[cfg(test)]
#[path = "dispatch_matrix_test.rs"]
mod dispatch_matrix_test;
