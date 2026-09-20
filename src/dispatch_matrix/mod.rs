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
//! producers. All of them compile through this module rather than through
//! construct-specific dispatch passes.
//! A producer supplies:
//!
//! - `Subject`s: root inputs plus projections that can be proven on branches.
//! - `Region` questions: value-space tests such as type membership, equality,
//!   tuple/list/map/bitstring shape, map-key presence, or a guard predicate.
//! - source-ordered `DispatchArm`s: conjunctions of region questions that prove
//!   one opaque `Outcome`.
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
//!
//! `dispatch_matrix::demand` is the lattice a question is measured in: what a
//! test asks of one input, shaped like the value it asks about. It lives here
//! because the questions define it; the keying jobs only join it across bodies.
//! The graph builder folds every question it is handed into
//! `DispatchGraph::input_demand`, one slot per declared input, so a finished
//! plan states what it reads of its inputs and no reader walks the graph to
//! rediscover it.

use std::collections::BTreeMap;

pub(crate) mod demand;
pub(crate) mod pattern;

use demand::{DemandPathStep, DispatchDemand, demand_at_step};

/// The dispatch/pattern constant carrier. `dispatch_matrix` is otherwise
/// generic over an opaque `TypeHandle` and has no dependency on any concrete
/// value type; this re-export is the one intentional edge to
/// `crate::ground_value`, a dependency-free leaf, so dispatch questions can
/// name the ground literal a subject is tested against.
pub(crate) use crate::ground_value::GroundValue;

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct PreparedKeyId(pub(crate) u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DispatchMatrix<TypeHandle> {
    pub(crate) subjects: Vec<Subject>,
    pub(crate) outcomes: Vec<Outcome>,
    pub(crate) arms: Vec<DispatchArm<TypeHandle>>,
}

#[cfg(test)]
impl<TypeHandle> DispatchMatrix<TypeHandle> {
    pub(crate) fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> DispatchMatrix<MappedHandle> {
        DispatchMatrix {
            subjects: self.subjects.clone(),
            outcomes: self.outcomes.clone(),
            arms: self.arms.iter().map(|arm| arm.map_type_handle(map)).collect(),
        }
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
    StructField(String),
    ListHead,
    ListTail,
    MapValue { key: GroundValue },
    BitstringField(BitstringExtraction),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DispatchArm<TypeHandle> {
    pub(crate) id: ArmId,
    pub(crate) questions: Vec<RegionQuestion<TypeHandle>>,
    pub(crate) evidence: EdgeEvidence<TypeHandle>,
    pub(crate) outcome: OutcomeId,
}

#[cfg(test)]
impl<TypeHandle> DispatchArm<TypeHandle> {
    fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> DispatchArm<MappedHandle> {
        DispatchArm {
            id: self.id,
            questions: self
                .questions
                .iter()
                .map(|question| question.map_type_handle(map))
                .collect(),
            evidence: self.evidence.map_type_handle(map),
            outcome: self.outcome,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RegionPredicate<TypeHandle> {
    pub(crate) subject: SubjectId,
    pub(crate) region: Region<TypeHandle>,
}

impl<TypeHandle> RegionPredicate<TypeHandle> {
    pub(crate) fn new(subject: SubjectId, region: Region<TypeHandle>) -> Self {
        Self { subject, region }
    }

    pub(crate) fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> RegionPredicate<MappedHandle> {
        RegionPredicate {
            subject: self.subject,
            region: self.region.map_type_handle(map),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Region<TypeHandle> {
    Type(TypeHandle),
    Equal(ComparisonValue),
    TupleArity(u32),
    List(ListRegion),
    MapKind,
    MapKeyPresent { key: GroundValue },
    Bitstring(BitstringShape),
    Guard(GuardId),
}

impl<TypeHandle> Region<TypeHandle> {
    pub(crate) fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> Region<MappedHandle> {
        match self {
            Region::Type(ty) => Region::Type(map(ty)),
            Region::Equal(value) => Region::Equal(value.clone()),
            Region::TupleArity(arity) => Region::TupleArity(*arity),
            Region::List(region) => Region::List(*region),
            Region::MapKind => Region::MapKind,
            Region::MapKeyPresent { key } => Region::MapKeyPresent { key: key.clone() },
            Region::Bitstring(shape) => Region::Bitstring(shape.clone()),
            Region::Guard(guard) => Region::Guard(*guard),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ComparisonValue {
    Const(GroundValue),
    Pinned(PinnedValueId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ListRegion {
    Empty,
    Cons,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BitstringShape {
    pub(crate) fields: Vec<SubjectId>,
    pub(crate) require_done: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct BitstringExtraction {
    pub(crate) previous: Option<SubjectId>,
    pub(crate) spec: BitstringFieldShape,
    pub(crate) is_last: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct BitstringFieldShape {
    pub(crate) kind: BitstringFieldKind,
    pub(crate) size: Option<BitstringFieldSize>,
    pub(crate) endian: BitstringEndian,
    pub(crate) signed: bool,
    pub(crate) unit: Option<u32>,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum BitstringFieldSize {
    Literal(u32),
    /// A size bound by an EARLIER FIELD of the same bitstring, which the
    /// dispatch has already extracted: `<<n, s :: binary-size(n)>>`.
    Binding(SubjectId),
    /// A size bound BEFORE THE PATTERN BEGAN, never a parameter of the same
    /// head. It reaches dispatch the same way a pinned value does, because
    /// that is the same question: a name the pattern uses but does not bind.
    Pinned(PinnedValueId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum BitstringEndian {
    Big,
    Little,
    Native,
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EdgeEvidence<TypeHandle> {
    pub(crate) proofs: Vec<Proof<TypeHandle>>,
    pub(crate) projections: Vec<SubjectId>,
}

impl<TypeHandle> Default for EdgeEvidence<TypeHandle> {
    fn default() -> Self {
        Self {
            proofs: Vec::new(),
            projections: Vec::new(),
        }
    }
}

impl<TypeHandle> EdgeEvidence<TypeHandle> {
    pub(crate) fn empty() -> Self {
        Self::default()
    }

    pub(crate) fn from_proof(predicate: RegionPredicate<TypeHandle>, sense: ProofSense) -> Self {
        Self {
            proofs: vec![Proof { predicate, sense }],
            projections: Vec::new(),
        }
    }

    pub(crate) fn with_projection(mut self, projection: SubjectId) -> Self {
        self.projections.push(projection);
        self
    }

    pub(crate) fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> EdgeEvidence<MappedHandle> {
        EdgeEvidence {
            proofs: self.proofs.iter().map(|proof| proof.map_type_handle(map)).collect(),
            projections: self.projections.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Proof<TypeHandle> {
    pub(crate) predicate: RegionPredicate<TypeHandle>,
    pub(crate) sense: ProofSense,
}

impl<TypeHandle> Proof<TypeHandle> {
    pub(crate) fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> Proof<MappedHandle> {
        Proof {
            predicate: self.predicate.map_type_handle(map),
            sense: self.sense,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProofSense {
    Holds,
    DoesNotHold,
}

/// One normalized branch question over one subject.
///
/// This is the DispatchMatrix-level vocabulary. It names the semantic region
/// being tested and the evidence each branch produces. Existing backend
/// primitives are lowering choices for these questions, not additional semantic
/// variants in this model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RegionQuestion<TypeHandle> {
    pub(crate) predicate: RegionPredicate<TypeHandle>,
    pub(crate) match_evidence: EdgeEvidence<TypeHandle>,
    pub(crate) miss_evidence: EdgeEvidence<TypeHandle>,
}

impl<TypeHandle: Clone> RegionQuestion<TypeHandle> {
    pub(crate) fn new(predicate: RegionPredicate<TypeHandle>) -> Self {
        Self {
            match_evidence: EdgeEvidence::from_proof(predicate.clone(), ProofSense::Holds),
            miss_evidence: EdgeEvidence::from_proof(predicate.clone(), ProofSense::DoesNotHold),
            predicate,
        }
    }

    pub(crate) fn type_region(subject: SubjectId, ty: TypeHandle) -> Self {
        Self::new(RegionPredicate::new(subject, Region::Type(ty)))
    }

    pub(crate) fn into_test_node(self, on_match: GraphNodeId, on_miss: GraphNodeId) -> DispatchNode<TypeHandle> {
        DispatchNode::Test {
            predicate: self.predicate,
            on_match: DispatchEdge::with_evidence(on_match, self.match_evidence),
            on_miss: DispatchEdge::with_evidence(on_miss, self.miss_evidence),
        }
    }
}

impl<TypeHandle> RegionQuestion<TypeHandle> {
    pub(crate) fn equality(subject: SubjectId, value: ComparisonValue) -> Self {
        let match_predicate = RegionPredicate::new(subject, Region::Equal(value.clone()));
        let miss_predicate = RegionPredicate::new(subject, Region::Equal(value.clone()));
        let predicate = RegionPredicate::new(subject, Region::Equal(value));
        Self {
            match_evidence: EdgeEvidence::from_proof(match_predicate, ProofSense::Holds),
            miss_evidence: EdgeEvidence::from_proof(miss_predicate, ProofSense::DoesNotHold),
            predicate,
        }
    }

    pub(crate) fn list_empty(subject: SubjectId) -> Self {
        let match_predicate = RegionPredicate::new(subject, Region::List(ListRegion::Empty));
        let miss_predicate = RegionPredicate::new(subject, Region::List(ListRegion::Empty));
        let predicate = RegionPredicate::new(subject, Region::List(ListRegion::Empty));
        Self {
            match_evidence: EdgeEvidence::from_proof(match_predicate, ProofSense::Holds),
            miss_evidence: EdgeEvidence::from_proof(miss_predicate, ProofSense::DoesNotHold),
            predicate,
        }
    }

    pub(crate) fn tuple_arity(subject: SubjectId, arity: u32, fields: impl IntoIterator<Item = SubjectId>) -> Self {
        let mut match_evidence = EdgeEvidence::from_proof(
            RegionPredicate::new(subject, Region::TupleArity(arity)),
            ProofSense::Holds,
        );
        for result in fields {
            match_evidence = match_evidence.with_projection(result);
        }
        let miss_predicate = RegionPredicate::new(subject, Region::TupleArity(arity));
        let predicate = RegionPredicate::new(subject, Region::TupleArity(arity));
        Self {
            match_evidence,
            miss_evidence: EdgeEvidence::from_proof(miss_predicate, ProofSense::DoesNotHold),
            predicate,
        }
    }

    pub(crate) fn list_cons(subject: SubjectId, head: SubjectId, tail: SubjectId) -> Self {
        let predicate = RegionPredicate::new(subject, Region::List(ListRegion::Cons));
        let miss_predicate = RegionPredicate::new(subject, Region::List(ListRegion::Cons));
        Self {
            match_evidence: EdgeEvidence::from_proof(
                RegionPredicate::new(subject, Region::List(ListRegion::Cons)),
                ProofSense::Holds,
            )
            .with_projection(head)
            .with_projection(tail),
            miss_evidence: EdgeEvidence::from_proof(miss_predicate, ProofSense::DoesNotHold),
            predicate,
        }
    }

    pub(crate) fn map_key_present(subject: SubjectId, key: GroundValue, value: SubjectId) -> Self {
        let predicate = RegionPredicate::new(subject, Region::MapKeyPresent { key: key.clone() });
        let match_key = key.clone();
        let miss_key = key;
        Self {
            match_evidence: EdgeEvidence::from_proof(
                RegionPredicate::new(subject, Region::MapKeyPresent { key: match_key }),
                ProofSense::Holds,
            )
            .with_projection(value),
            miss_evidence: EdgeEvidence::from_proof(
                RegionPredicate::new(subject, Region::MapKeyPresent { key: miss_key }),
                ProofSense::DoesNotHold,
            ),
            predicate,
        }
    }
}

#[cfg(test)]
impl<TypeHandle> RegionQuestion<TypeHandle> {
    fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> RegionQuestion<MappedHandle> {
        RegionQuestion {
            predicate: self.predicate.map_type_handle(map),
            match_evidence: self.match_evidence.map_type_handle(map),
            miss_evidence: self.miss_evidence.map_type_handle(map),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DispatchGraph<TypeHandle> {
    /// The declared inputs and branch-proven projections its nodes name.
    pub(crate) subjects: Vec<Subject>,
    pub(crate) nodes: Vec<DispatchNode<TypeHandle>>,
    pub(crate) root: GraphNodeId,
    /// What the graph's questions ask of each declared input, one slot per
    /// input, folded as the nodes were added.
    pub(crate) input_demand: Vec<DispatchDemand>,
}

impl<TypeHandle> DispatchGraph<TypeHandle> {
    pub(crate) fn subject(&self, id: SubjectId) -> Option<&Subject> {
        self.subjects.get(id.0 as usize)
    }

    pub(crate) fn node(&self, id: GraphNodeId) -> Option<&DispatchNode<TypeHandle>> {
        self.nodes.get(id.0 as usize)
    }

    pub(crate) fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> DispatchGraph<MappedHandle> {
        DispatchGraph {
            subjects: self.subjects.clone(),
            nodes: self.nodes.iter().map(|node| node.map_type_handle(map)).collect(),
            root: self.root,
            input_demand: self.input_demand.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DispatchNode<TypeHandle> {
    Fail,
    Outcome {
        outcome: OutcomeId,
        evidence: EdgeEvidence<TypeHandle>,
    },
    Test {
        predicate: RegionPredicate<TypeHandle>,
        on_match: DispatchEdge<TypeHandle>,
        on_miss: DispatchEdge<TypeHandle>,
    },
}

impl<TypeHandle> DispatchNode<TypeHandle> {
    pub(crate) fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> DispatchNode<MappedHandle> {
        match self {
            DispatchNode::Fail => DispatchNode::Fail,
            DispatchNode::Outcome { outcome, evidence } => DispatchNode::Outcome {
                outcome: *outcome,
                evidence: evidence.map_type_handle(map),
            },
            DispatchNode::Test {
                predicate,
                on_match,
                on_miss,
            } => DispatchNode::Test {
                predicate: predicate.map_type_handle(map),
                on_match: on_match.map_type_handle(map),
                on_miss: on_miss.map_type_handle(map),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DispatchEdge<TypeHandle> {
    pub(crate) target: GraphNodeId,
    pub(crate) evidence: EdgeEvidence<TypeHandle>,
}

impl<TypeHandle> DispatchEdge<TypeHandle> {
    #[cfg(test)]
    pub(crate) fn new(target: GraphNodeId) -> Self {
        Self {
            target,
            evidence: EdgeEvidence::empty(),
        }
    }

    pub(crate) fn with_evidence(target: GraphNodeId, evidence: EdgeEvidence<TypeHandle>) -> Self {
        Self { target, evidence }
    }

    pub(crate) fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> DispatchEdge<MappedHandle> {
        DispatchEdge {
            target: self.target,
            evidence: self.evidence.map_type_handle(map),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DispatchMatrixError {
    UnknownSubject(SubjectId),
    ExpectedProjection(SubjectId),
    UnknownOutcome(OutcomeId),
    UniqueOutcomeReused(OutcomeId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DispatchCompileError {
    InvalidGraph(DispatchGraphError),
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct DispatchCompileStats {
    pub(crate) arms: usize,
    pub(crate) test_nodes: usize,
    pub(crate) outcome_nodes: usize,
    pub(crate) fail_nodes: usize,
    pub(crate) shared_prefix_tests: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CompiledDispatchGraph<TypeHandle> {
    pub(crate) graph: DispatchGraph<TypeHandle>,
    pub(crate) stats: DispatchCompileStats,
}

#[derive(Debug, Clone)]
struct ArmCompileState<'a, TypeHandle> {
    arm: &'a DispatchArm<TypeHandle>,
    questions: Vec<RegionQuestion<TypeHandle>>,
}

/// Everything a question's demand is resolved against besides the matrix it is
/// compiling: how many inputs the plan declares, the input each pin arrives
/// on, and what each guard reads.
///
/// `count` is the DECLARED input count, not the number of input subjects the
/// matrix holds: a producer may mint a subject to carry a guard on a plan that
/// declares no inputs at all.
#[derive(Debug, Clone, Copy)]
pub(crate) struct PlanInputs<'a> {
    pub(crate) count: usize,
    /// The input each pinned value arrives on, when the rows' prematch bound it.
    pub(crate) pinned: &'a [Option<u32>],
    /// What each guard reads, in the plan's own subject and pin space.
    pub(crate) guard_leaves: &'a [Vec<GuardLeaf>],
}

/// One value a guard reads. A guard question rides a carrier subject, so what
/// a guard asks of the declared inputs is exactly its leaves.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GuardLeaf {
    Subject(SubjectId),
    Pinned(PinnedValueId),
}

pub(crate) fn compile_dispatch_matrix<TypeHandle: Clone + Eq>(
    matrix: DispatchMatrix<TypeHandle>,
    inputs: PlanInputs<'_>,
) -> Result<CompiledDispatchGraph<TypeHandle>, DispatchCompileError> {
    let DispatchMatrix {
        subjects,
        outcomes: _,
        arms,
    } = matrix;
    compile_ordered_arms(arms, subjects, inputs)
}

fn compile_ordered_arms<TypeHandle: Clone + Eq>(
    ordered_arms: Vec<DispatchArm<TypeHandle>>,
    subjects: Vec<Subject>,
    inputs: PlanInputs<'_>,
) -> Result<CompiledDispatchGraph<TypeHandle>, DispatchCompileError> {
    let mut stats = DispatchCompileStats {
        arms: ordered_arms.len(),
        ..DispatchCompileStats::default()
    };
    let mut builder = DispatchGraphBuilder::typed(subjects, inputs);
    let fallback = fallback_node(&mut builder, &mut stats);
    let states = ordered_arms
        .iter()
        .map(|arm| ArmCompileState {
            arm,
            questions: arm.questions.clone(),
        })
        .collect::<Vec<_>>();
    let root = compile_arm_sequence(&states, fallback, &mut builder, &mut stats);
    let graph = builder.build(root).map_err(DispatchCompileError::InvalidGraph)?;
    Ok(CompiledDispatchGraph { graph, stats })
}

fn fallback_node<TypeHandle: Clone + Eq>(
    builder: &mut DispatchGraphBuilder<'_, TypeHandle>,
    stats: &mut DispatchCompileStats,
) -> GraphNodeId {
    stats.fail_nodes += 1;
    builder.add_node(DispatchNode::Fail)
}

fn compile_arm_sequence<TypeHandle: Clone + Eq>(
    arms: &[ArmCompileState<'_, TypeHandle>],
    fallback: GraphNodeId,
    builder: &mut DispatchGraphBuilder<'_, TypeHandle>,
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

fn compile_single_arm<TypeHandle: Clone + Eq>(
    arm: &ArmCompileState<'_, TypeHandle>,
    on_miss: GraphNodeId,
    builder: &mut DispatchGraphBuilder<'_, TypeHandle>,
    stats: &mut DispatchCompileStats,
) -> GraphNodeId {
    let mut current = outcome_node(arm.arm, builder, stats);
    for question in arm.questions.iter().rev() {
        current = test_node(question.clone(), current, on_miss, builder, stats);
    }
    current
}

fn outcome_node<TypeHandle: Clone + Eq>(
    arm: &DispatchArm<TypeHandle>,
    builder: &mut DispatchGraphBuilder<'_, TypeHandle>,
    stats: &mut DispatchCompileStats,
) -> GraphNodeId {
    stats.outcome_nodes += 1;
    builder.add_node(DispatchNode::Outcome {
        outcome: arm.outcome,
        evidence: arm.evidence.clone(),
    })
}

fn test_node<TypeHandle: Clone + Eq>(
    question: RegionQuestion<TypeHandle>,
    on_match: GraphNodeId,
    on_miss: GraphNodeId,
    builder: &mut DispatchGraphBuilder<'_, TypeHandle>,
    stats: &mut DispatchCompileStats,
) -> GraphNodeId {
    stats.test_nodes += 1;
    builder.add_node(question.into_test_node(on_match, on_miss))
}

pub(crate) struct DispatchMatrixBuilder<TypeHandle> {
    subjects: Vec<Subject>,
    input_count: u32,
    outcomes: Vec<Outcome>,
    arms: Vec<DispatchArm<TypeHandle>>,
    outcome_uses: BTreeMap<OutcomeId, usize>,
}

impl<TypeHandle> DispatchMatrixBuilder<TypeHandle> {
    fn empty() -> Self {
        Self {
            subjects: Vec::new(),
            input_count: 0,
            outcomes: Vec::new(),
            arms: Vec::new(),
            outcome_uses: BTreeMap::new(),
        }
    }
}

impl<TypeHandle: Clone + Eq> DispatchMatrixBuilder<TypeHandle> {
    pub(crate) fn typed() -> Self {
        Self::empty()
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
        questions: Vec<RegionQuestion<TypeHandle>>,
        evidence: EdgeEvidence<TypeHandle>,
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

    pub(crate) fn build(self) -> Result<DispatchMatrix<TypeHandle>, DispatchMatrixError> {
        Ok(DispatchMatrix {
            subjects: self.subjects,
            outcomes: self.outcomes,
            arms: self.arms,
        })
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

    fn ensure_evidence_subjects(&self, evidence: &EdgeEvidence<TypeHandle>) -> Result<(), DispatchMatrixError> {
        for proof in &evidence.proofs {
            self.ensure_subject(proof.predicate.subject)?;
        }
        for projection in &evidence.projections {
            self.ensure_subject(*projection)?;
            if !matches!(
                self.subjects[projection.0 as usize].source,
                SubjectSource::Projection(_)
            ) {
                return Err(DispatchMatrixError::ExpectedProjection(*projection));
            }
        }
        Ok(())
    }

    fn ensure_question_subjects(&self, question: &RegionQuestion<TypeHandle>) -> Result<(), DispatchMatrixError> {
        self.ensure_subject(question.predicate.subject)?;
        self.ensure_evidence_subjects(&question.match_evidence)?;
        self.ensure_evidence_subjects(&question.miss_evidence)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DispatchGraphError {
    UnknownNode(GraphNodeId),
}

pub(crate) struct DispatchGraphBuilder<'a, TypeHandle> {
    subjects: Vec<Subject>,
    nodes: Vec<DispatchNode<TypeHandle>>,
    inputs: PlanInputs<'a>,
    input_demand: Vec<DispatchDemand>,
}

impl<'a, TypeHandle: Clone + Eq> DispatchGraphBuilder<'a, TypeHandle> {
    pub(crate) fn typed(subjects: Vec<Subject>, inputs: PlanInputs<'a>) -> Self {
        Self {
            subjects,
            nodes: Vec::new(),
            input_demand: vec![DispatchDemand::Ignore; inputs.count],
            inputs,
        }
    }

    pub(crate) fn add_node(&mut self, node: DispatchNode<TypeHandle>) -> GraphNodeId {
        self.charge_node(&node);
        let id = GraphNodeId(self.nodes.len() as u32);
        self.nodes.push(node);
        id
    }

    pub(crate) fn build(self, root: GraphNodeId) -> Result<DispatchGraph<TypeHandle>, DispatchGraphError> {
        self.ensure_node(root)?;
        for node in &self.nodes {
            if let DispatchNode::Test { on_match, on_miss, .. } = node {
                self.ensure_node(on_match.target)?;
                self.ensure_node(on_miss.target)?;
            }
        }
        self.ensure_projections_ride_a_charged_input();
        Ok(DispatchGraph {
            subjects: self.subjects,
            nodes: self.nodes,
            root,
            input_demand: self.input_demand,
        })
    }

    fn ensure_node(&self, id: GraphNodeId) -> Result<(), DispatchGraphError> {
        self.nodes
            .get(id.0 as usize)
            .map(|_| ())
            .ok_or(DispatchGraphError::UnknownNode(id))
    }

    /// Charges what one node asks of the declared inputs.
    ///
    /// Only a test asks anything. Edge evidence does not: a proof restates the
    /// test's own predicate, and a projection is a binding reached by a test
    /// that already charged its root.
    fn charge_node(&mut self, node: &DispatchNode<TypeHandle>) {
        let DispatchNode::Test { predicate, .. } = node else {
            return;
        };
        // A guard question rides a carrier subject the guard need not read, so
        // the carrier is not charged: the guard's leaves say what it reads.
        if let Region::Guard(guard) = &predicate.region {
            self.charge_guard(*guard);
            return;
        }
        self.charge_subject(predicate.subject, demand_for_region(&predicate.region));
        match &predicate.region {
            Region::Equal(ComparisonValue::Pinned(pinned)) => self.charge_pin(*pinned),
            Region::Bitstring(shape) => self.charge_bitstring_sizes(shape),
            _ => {}
        }
    }

    fn charge_guard(&mut self, guard: GuardId) {
        let guard_leaves = self.inputs.guard_leaves;
        let Some(leaves) = guard_leaves.get(guard.0 as usize) else {
            return;
        };
        for leaf in leaves {
            match leaf {
                GuardLeaf::Subject(subject) => self.charge_subject(*subject, DispatchDemand::Whole),
                GuardLeaf::Pinned(pinned) => self.charge_pin(*pinned),
            }
        }
    }

    /// A bitstring field whose size was bound before the pattern began reads
    /// the input that delivers the pin, on top of the bitstring itself.
    fn charge_bitstring_sizes(&mut self, shape: &BitstringShape) {
        for field in &shape.fields {
            let pinned = self
                .subjects
                .get(field.0 as usize)
                .and_then(|subject| match &subject.source {
                    SubjectSource::Projection(projection) => match &projection.kind {
                        ProjectionKind::BitstringField(extraction) => match &extraction.spec.size {
                            Some(BitstringFieldSize::Pinned(pinned)) => Some(*pinned),
                            _ => None,
                        },
                        _ => None,
                    },
                    _ => None,
                });
            if let Some(pinned) = pinned {
                self.charge_pin(pinned);
            }
        }
    }

    /// A pin the rows' prematch bound reads the input that delivers it.
    fn charge_pin(&mut self, pinned: PinnedValueId) {
        if let Some(Some(input)) = self.inputs.pinned.get(pinned.0 as usize).copied() {
            self.charge_input(input, DispatchDemand::Whole);
        }
    }

    fn charge_subject(&mut self, subject: SubjectId, demand: DispatchDemand) {
        let (ordinal, demand) = self.subject_demand(subject, demand);
        self.charge_input(ordinal, demand);
    }

    /// The input a subject descends from, and what a demand on that subject
    /// asks of that input.
    fn subject_demand(&self, subject: SubjectId, demand: DispatchDemand) -> (u32, DispatchDemand) {
        subject_demand(&self.subjects, subject, demand).unwrap_or_else(|| missing_subject(subject))
    }

    /// The input a subject descends from, for a caller that asks nothing of it.
    fn subject_root(&self, subject: SubjectId) -> u32 {
        subject_root(&self.subjects, subject).unwrap_or_else(|| missing_subject(subject))
    }

    /// Every ordinal charged here names a declared input of THIS plan. A
    /// backend is entitled to pass anything else as nil, so an ordinal that
    /// escapes the declared count is not a conservative over-approximation --
    /// it is a demand no caller can meet. The assertion keeps that failure at
    /// the plan that produced it instead of at whichever door reads it first.
    fn charge_input(&mut self, ordinal: u32, demand: DispatchDemand) {
        let count = self.inputs.count;
        let slot = self
            .input_demand
            .get_mut(ordinal as usize)
            .unwrap_or_else(|| panic!("dispatch plan requires input {ordinal} but has only {count} semantic input(s)"));
        slot.join_assign(demand);
    }

    /// A projection is a binding, not a question: it names where a value comes
    /// from once a test on its source has succeeded. Every projection therefore
    /// sits under a test that charged its root input, which is what entitles
    /// the fold to ignore evidence.
    fn ensure_projections_ride_a_charged_input(&self) {
        for node in &self.nodes {
            let (first, second) = match node {
                DispatchNode::Fail => (None, None),
                DispatchNode::Outcome { evidence, .. } => (Some(evidence), None),
                DispatchNode::Test { on_match, on_miss, .. } => (Some(&on_match.evidence), Some(&on_miss.evidence)),
            };
            for projection in first
                .into_iter()
                .chain(second)
                .flat_map(|evidence| &evidence.projections)
            {
                let ordinal = self.subject_root(*projection);
                assert!(
                    self.input_demand
                        .get(ordinal as usize)
                        .is_some_and(DispatchDemand::asks_anything),
                    "dispatch projects from input {ordinal}, which no question charged",
                );
            }
        }
    }
}

/// What one question asks of the value it tests.
fn demand_for_region<TypeHandle>(region: &Region<TypeHandle>) -> DispatchDemand {
    match region {
        Region::List(ListRegion::Empty | ListRegion::Cons) => DispatchDemand::ListShape,
        Region::TupleArity(_) => DispatchDemand::TupleFields,
        Region::Equal(_)
        | Region::Type(_)
        | Region::MapKind
        | Region::MapKeyPresent { .. }
        | Region::Bitstring(_)
        | Region::Guard(_) => DispatchDemand::Whole,
    }
}

/// A question the matrix accepted names a subject the matrix holds, so an
/// unknown subject is a producer that built the graph from another plan's
/// questions.
fn missing_subject(subject: SubjectId) -> ! {
    panic!(
        "dispatch question names subject s{}, which its matrix does not hold",
        subject.0
    )
}

/// The input a subject descends from. A projection names its source, so the
/// chain climbs to the input the subject was carved out of.
fn subject_root(subjects: &[Subject], mut subject: SubjectId) -> Option<u32> {
    loop {
        match &subjects.get(subject.0 as usize)?.source {
            SubjectSource::Input { ordinal } => return Some(*ordinal),
            SubjectSource::Projection(projection) => subject = projection.source,
        }
    }
}

/// The input a subject descends from, and what a demand on that subject asks
/// of that input.
///
/// The walk climbs the same chain as `subject_root`, and each step it climbs
/// restates the demand as what that step asks of the value it was taken from.
/// The step nearest the input therefore decides what the input carries: a
/// question about the head of a list held in field 0 asks the input about a
/// tuple, not about a list.
fn subject_demand(
    subjects: &[Subject],
    mut subject: SubjectId,
    mut demand: DispatchDemand,
) -> Option<(u32, DispatchDemand)> {
    loop {
        match &subjects.get(subject.0 as usize)?.source {
            SubjectSource::Input { ordinal } => return Some((*ordinal, demand)),
            SubjectSource::Projection(projection) => {
                demand = demand_at_step(&DemandPathStep::from(&projection.kind));
                subject = projection.source;
            }
        }
    }
}

#[cfg(test)]
#[path = "dispatch_matrix_test.rs"]
mod dispatch_matrix_test;
