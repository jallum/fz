//! Shared model for compiling ordered semantic dispatch into an executable
//! decision graph.
//!
//! This module is directly indebted to Luc Maranget's "Compiling Pattern
//! Matching to Good Decision Trees" (ML'08):
//! <http://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf>.
//! Maranget's central lesson for us is the separation between a source-level
//! collection of rows and a lower-level decision tree: choose tests over
//! subterms, preserve source priority, avoid retesting the same projected value,
//! and share common decision structure where doing so keeps the generated code
//! compact.
//!
//! `DispatchMatrix` keeps that decision-tree spine but makes the row language
//! more general than ML constructor patterns. Function heads, `case`, `with`
//! `else`, selective receive, and guard helper dispatch are source-pattern
//! producers over `Order::Source`; protocol dispatch is a type-region producer
//! over `Order::Specificity` or an explicit residual order. All of them compile
//! through this module rather than through construct-specific dispatch passes.
//! A producer supplies:
//!
//! - `Subject`s: root inputs plus projections that can be proven on branches.
//! - `Region` questions: value-space tests such as type membership, equality,
//!   tuple/list/map/bitstring shape, map-key presence, or a guard predicate.
//! - ordered `DispatchArm`s: conjunctions of region questions that prove one
//!   opaque `Outcome`.
//! - an `Order`: source priority for pattern matching, type specificity for
//!   closed protocol/type dispatch, or an explicit materialized order.
//!
//! The compiler then lowers those arms into a `DispatchGraph`. The graph is
//! intentionally producer-neutral: it decides only which outcome wins or that
//! dispatch failed. What a win means remains outside this module. Function
//! heads, `case`, and `with else` map source-pattern outcomes to continuation
//! bodies and bindings; selective receive maps outcomes to mailbox accept/reject
//! behavior; protocol dispatch maps outcomes to direct calls or residual
//! fallback.
//!
//! Branch-local evidence is the main correctness boundary. A successful
//! `List(Cons)` edge can project `ListHead` and `ListTail`; a successful
//! `TupleArity(2)` edge can project tuple fields; a successful
//! `MapKeyPresent` edge can project the map value, including `nil`. The miss
//! edge does not get those projections. Lowering and codegen consume this
//! evidence directly instead of re-deriving safety from syntax, which keeps
//! test-first/project-second semantics correct by construction.
//!
//! `dispatch_matrix::pattern` is now just a producer on top of this model. Its
//! `SourcePatternRows` are AST-facing input rows; they are not a second matcher
//! model, and they do not own executable dispatch semantics.

use crate::types::{Ty, Types};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) mod pattern;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct SubjectId(pub(crate) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct ArmId(pub(crate) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct OutcomeId(pub(crate) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct GraphNodeId(pub(crate) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct GuardId(pub(crate) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct PinnedValueId(pub(crate) u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct DispatchMatrix {
    pub(crate) subjects: Vec<Subject>,
    pub(crate) outcomes: Vec<Outcome>,
    pub(crate) arms: Vec<DispatchArm>,
    pub(crate) order: Order,
}

impl DispatchMatrix {
    #[cfg(test)]
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Subject {
    pub(crate) id: SubjectId,
    pub(crate) source: SubjectSource,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum SubjectSource {
    Input { ordinal: u32 },
    Projection(SubjectProjection),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SubjectProjection {
    pub(crate) source: SubjectId,
    pub(crate) kind: ProjectionKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum ProjectionKind {
    TupleField(u32),
    ListHead,
    ListTail,
    MapValue { key: DispatchConst },
    BitstringField(u32),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct DispatchArm {
    pub(crate) id: ArmId,
    pub(crate) questions: Vec<RegionQuestion>,
    pub(crate) evidence: EdgeEvidence,
    pub(crate) outcome: OutcomeId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct RegionPredicate {
    pub(crate) subject: SubjectId,
    pub(crate) region: Region,
}

impl RegionPredicate {
    pub(crate) fn new(subject: SubjectId, region: Region) -> Self {
        Self { subject, region }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum Region {
    #[allow(dead_code)] // Permanent top-region vocabulary; current producers emit concrete regions.
    Any,
    #[allow(dead_code)] // Permanent bottom-region vocabulary used by model tests and future residuals.
    Never,
    Type(Ty),
    Equal(ComparisonValue),
    TupleArity(u32),
    List(ListRegion),
    MapKind,
    MapKeyPresent {
        key: DispatchConst,
    },
    Bitstring(BitstringShape),
    Guard(GuardId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum ComparisonValue {
    Const(DispatchConst),
    Pinned(PinnedValueId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum ListRegion {
    Empty,
    Cons,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct BitstringShape {
    pub(crate) fields: Vec<BitstringFieldShape>,
    pub(crate) require_done: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct BitstringFieldShape {
    pub(crate) kind: BitstringFieldKind,
    pub(crate) size: Option<BitstringFieldSize>,
    pub(crate) endian: BitstringEndian,
    pub(crate) signed: bool,
    pub(crate) unit: Option<u32>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum BitstringFieldKind {
    Integer,
    Float,
    Binary,
    Bits,
    Utf8,
    Utf16,
    Utf32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum BitstringFieldSize {
    Literal(u32),
    Binding(SubjectId),
    BindingName(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum BitstringEndian {
    Big,
    Little,
    Native,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) enum DispatchConst {
    Int(i64),
    FloatBits(u64),
    AtomName(String),
    Bool(bool),
    Nil,
    EmptyList,
    Utf8Binary(Vec<u8>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum Order {
    /// Source-pattern semantics: first matching arm wins.
    Source,
    /// Type-dispatch semantics: more-specific regions win; incomparable
    /// overlaps are diagnosed by later analysis.
    Specificity,
    /// A fully materialized order. Useful for tests and future graph snapshots.
    #[allow(dead_code)] // Explicit orders are model vocabulary; production producers use Source/Specificity today.
    Explicit(Vec<ArmId>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Outcome {
    pub(crate) id: OutcomeId,
    pub(crate) multiplicity: OutcomeMultiplicity,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum OutcomeMultiplicity {
    /// At most one arm may route to this outcome.
    Unique,
    /// Multiple arms may share this outcome.
    #[allow(dead_code)] // Shared outcomes are part of the model; current producers mostly mint unique outcomes.
    Shared,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Proof {
    pub(crate) predicate: RegionPredicate,
    pub(crate) sense: ProofSense,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum ProofSense {
    Holds,
    DoesNotHold,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
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
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
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

    pub(crate) fn tuple_arity(subject: SubjectId, arity: u32, fields: impl IntoIterator<Item = SubjectId>) -> Self {
        let predicate = RegionPredicate::new(subject, Region::TupleArity(arity));
        let mut match_evidence = EdgeEvidence::from_proof(predicate.clone(), ProofSense::Holds);
        for (index, result) in fields.into_iter().enumerate() {
            match_evidence = match_evidence.with_projection(EdgeProjection {
                source: subject,
                kind: ProjectionKind::TupleField(index as u32),
                result,
            });
        }
        Self {
            match_evidence,
            miss_evidence: EdgeEvidence::from_proof(predicate.clone(), ProofSense::DoesNotHold),
            predicate,
        }
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct DispatchGraph {
    pub(crate) nodes: Vec<DispatchNode>,
    pub(crate) root: GraphNodeId,
}

impl DispatchGraph {
    pub(crate) fn node(&self, id: GraphNodeId) -> Option<&DispatchNode> {
        self.nodes.get(id.0 as usize)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct DispatchEdge {
    pub(crate) target: GraphNodeId,
    pub(crate) evidence: EdgeEvidence,
}

impl DispatchEdge {
    #[cfg(test)]
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
    MatrixBuild(DispatchMatrixError),
    NonTypeArmInSpecificityOrder(ArmId),
    TypeOrderDiagnostics(Vec<TypeRegionDiagnostic>),
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
    compile_ordered_arms(matrix, ordered_arms, options)
}

pub(crate) fn compile_dispatch_matrix_with_type_order<T: Types<Ty = Ty>>(
    t: &mut T,
    matrix: &DispatchMatrix,
    options: DispatchCompileOptions,
    equal_policy: EqualTypeRegionPolicy,
) -> Result<CompiledDispatchGraph, DispatchCompileError> {
    let ordered_arms = ordered_arms_with_type_order(t, matrix, equal_policy)?;
    compile_ordered_arms(matrix, ordered_arms, options)
}

fn compile_ordered_arms(
    matrix: &DispatchMatrix,
    ordered_arms: Vec<&DispatchArm>,
    options: DispatchCompileOptions,
) -> Result<CompiledDispatchGraph, DispatchCompileError> {
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

fn ordered_arms_with_type_order<'a, T: Types<Ty = Ty>>(
    t: &mut T,
    matrix: &'a DispatchMatrix,
    equal_policy: EqualTypeRegionPolicy,
) -> Result<Vec<&'a DispatchArm>, DispatchCompileError> {
    match &matrix.order {
        Order::Specificity => {
            let type_arms = type_region_arms_from_matrix(matrix)?;
            let analysis = analyze_type_region_arms(t, &type_arms, equal_policy);
            let blocking = analysis
                .diagnostics
                .iter()
                .filter(|diag| {
                    matches!(
                        diag.kind,
                        TypeRegionDiagnosticKind::AmbiguousEqualRegions | TypeRegionDiagnosticKind::AmbiguousOverlap
                    )
                })
                .cloned()
                .collect::<Vec<_>>();
            if !blocking.is_empty() {
                return Err(DispatchCompileError::TypeOrderDiagnostics(blocking));
            }
            analysis
                .ordered_arms
                .iter()
                .map(|&id| matrix.arm(id).ok_or(DispatchCompileError::UnknownArm(id)))
                .collect()
        }
        _ => ordered_arms(matrix),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TypeRegionRelation {
    Equal,
    LeftMoreSpecific,
    RightMoreSpecific,
    Disjoint,
    OverlapAmbiguous,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EqualTypeRegionPolicy {
    DuplicateCoverage,
    #[allow(dead_code)] // Ambiguity policy is model-tested; production protocol dispatch treats equals as duplicates.
    Ambiguous,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TypeRegionDiagnosticKind {
    DuplicateCoverage,
    AmbiguousEqualRegions,
    AmbiguousOverlap,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TypeRegionDiagnostic {
    pub(crate) kind: TypeRegionDiagnosticKind,
    pub(crate) left: ArmId,
    pub(crate) right: ArmId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TypeRegionPair {
    pub(crate) left: ArmId,
    pub(crate) right: ArmId,
    pub(crate) relation: TypeRegionRelation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TypeRegionArm {
    pub(crate) arm: ArmId,
    pub(crate) subject: SubjectId,
    pub(crate) ty: Ty,
    pub(crate) outcome: OutcomeId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TypeRegionAnalysis {
    pub(crate) ordered_arms: Vec<ArmId>,
    pub(crate) pairs: Vec<TypeRegionPair>,
    pub(crate) diagnostics: Vec<TypeRegionDiagnostic>,
}

#[allow(dead_code)] // Type coverage is a DispatchMatrix model signal; protocol lowering stores the bool it needs today.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TypeCoverageStatus {
    Closed,
    Open,
}

#[allow(dead_code)] // See TypeCoverageStatus: retained as the typed result of coverage analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TypeCoverage {
    pub(crate) domain: Ty,
    pub(crate) covered: Ty,
    pub(crate) residual: Ty,
    pub(crate) status: TypeCoverageStatus,
}

pub(crate) fn type_region_relation<T: Types<Ty = Ty>>(t: &T, left: &Ty, right: &Ty) -> TypeRegionRelation {
    if t.is_equivalent(left, right) {
        TypeRegionRelation::Equal
    } else if t.is_disjoint(left, right) {
        TypeRegionRelation::Disjoint
    } else if t.is_subtype(left, right) {
        TypeRegionRelation::LeftMoreSpecific
    } else if t.is_subtype(right, left) {
        TypeRegionRelation::RightMoreSpecific
    } else {
        TypeRegionRelation::OverlapAmbiguous
    }
}

pub(crate) fn analyze_type_region_arms<T: Types<Ty = Ty>>(
    t: &mut T,
    arms: &[TypeRegionArm],
    equal_policy: EqualTypeRegionPolicy,
) -> TypeRegionAnalysis {
    let mut pairs = Vec::new();
    let mut diagnostics = Vec::new();
    for i in 0..arms.len() {
        for j in (i + 1)..arms.len() {
            let relation = type_region_relation(t, &arms[i].ty, &arms[j].ty);
            pairs.push(TypeRegionPair {
                left: arms[i].arm,
                right: arms[j].arm,
                relation,
            });
            match relation {
                TypeRegionRelation::Equal if arms[i].outcome != arms[j].outcome => {
                    let kind = match equal_policy {
                        EqualTypeRegionPolicy::DuplicateCoverage => TypeRegionDiagnosticKind::DuplicateCoverage,
                        EqualTypeRegionPolicy::Ambiguous => TypeRegionDiagnosticKind::AmbiguousEqualRegions,
                    };
                    diagnostics.push(TypeRegionDiagnostic {
                        kind,
                        left: arms[i].arm,
                        right: arms[j].arm,
                    });
                }
                TypeRegionRelation::OverlapAmbiguous => diagnostics.push(TypeRegionDiagnostic {
                    kind: TypeRegionDiagnosticKind::AmbiguousOverlap,
                    left: arms[i].arm,
                    right: arms[j].arm,
                }),
                _ => {}
            }
        }
    }

    let mut ordered = arms.to_vec();
    ordered.sort_by(|left, right| match type_region_relation(t, &left.ty, &right.ty) {
        TypeRegionRelation::LeftMoreSpecific => std::cmp::Ordering::Less,
        TypeRegionRelation::RightMoreSpecific => std::cmp::Ordering::Greater,
        _ => left.arm.cmp(&right.arm),
    });

    TypeRegionAnalysis {
        ordered_arms: ordered.into_iter().map(|arm| arm.arm).collect(),
        pairs,
        diagnostics,
    }
}

#[allow(dead_code)] // Coverage analysis is kept as tested model API even when producers consume simpler facts.
pub(crate) fn analyze_type_coverage<T: Types<Ty = Ty>>(t: &mut T, domain: Ty, arms: &[TypeRegionArm]) -> TypeCoverage {
    let mut covered = t.none();
    for arm in arms {
        let overlap = t.intersect(domain.clone(), arm.ty.clone());
        covered = t.union(covered, overlap);
    }
    let residual = t.difference(domain.clone(), covered.clone());
    let status = if t.is_empty(&residual) {
        TypeCoverageStatus::Closed
    } else {
        TypeCoverageStatus::Open
    };
    TypeCoverage {
        domain,
        covered,
        residual,
        status,
    }
}

fn type_region_arms_from_matrix(matrix: &DispatchMatrix) -> Result<Vec<TypeRegionArm>, DispatchCompileError> {
    matrix
        .arms
        .iter()
        .map(|arm| {
            let Some(question) = arm
                .questions
                .iter()
                .find(|question| matches!(question.predicate.region, Region::Type(_)))
            else {
                return Err(DispatchCompileError::NonTypeArmInSpecificityOrder(arm.id));
            };
            let Region::Type(ty) = &question.predicate.region else {
                unreachable!("question was filtered to type regions")
            };
            Ok(TypeRegionArm {
                arm: arm.id,
                subject: question.predicate.subject,
                ty: ty.clone(),
                outcome: arm.outcome,
            })
        })
        .collect()
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
