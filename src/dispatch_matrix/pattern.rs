use super::{
    BitstringEndian, BitstringFieldKind, BitstringFieldShape, BitstringFieldSize, BitstringShape, ComparisonValue,
    DispatchCompileError, DispatchCompileOptions, DispatchConst, DispatchGraph, DispatchMatrix, DispatchMatrixBuilder,
    DispatchMatrixError, DispatchNode, EdgeEvidence, EdgeProjection, GraphNodeId, GuardId, OutcomeId,
    OutcomeMultiplicity, PinnedValueId, ProjectionKind, Region, RegionPredicate, RegionQuestion, SubjectId,
    compile_dispatch_matrix,
};
use crate::exec::matcher::{
    GuardExpr, InputId, Matcher, MatcherBinding, MatcherBitField, MatcherBitSize, MatcherBitType, MatcherConst,
    MatcherEndian, MatcherInput, MatcherLeaf, MatcherNode, MatcherTest, NodeId, PinnedInput, SubjectRef, SwitchKey,
    SwitchKind,
};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternDispatchPlan {
    pub(crate) matrix: DispatchMatrix,
    pub(crate) graph: DispatchGraph,
    pub(crate) inputs: Vec<MatcherInput>,
    pub(crate) subjects: Vec<Option<SubjectRef>>,
    pub(crate) outcomes: Vec<PatternDispatchOutcome>,
    pub(crate) guards: Vec<GuardExpr>,
    pub(crate) pinned: Vec<PinnedInput>,
    pub(crate) prepared_keys: Vec<MatcherConst>,
    pub(crate) bitstring_direct_bindings: HashMap<SubjectId, Vec<String>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternDispatchOutcome {
    pub(crate) outcome: OutcomeId,
    pub(crate) body_id: u32,
    pub(crate) bindings: Vec<PatternDispatchBinding>,
    pub(crate) matcher_bindings: Vec<MatcherBinding>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternDispatchBinding {
    pub(crate) name: String,
    pub(crate) source: SubjectId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PatternDispatchError {
    UnknownMatcherNode(NodeId),
    UnknownInput(InputId),
    UnknownPreparedKey(u32),
    UnknownSubject(SubjectId),
    UnknownOutcome(OutcomeId),
    UnknownGuard(GuardId),
    UnknownGraphNode(GraphNodeId),
    MissingBitstringBindingName(SubjectId),
    UnsupportedSwitchCase { kind: SwitchKind, key: SwitchKey },
    UnsupportedRegion(Region),
    MatrixBuild(DispatchMatrixError),
    Compile(DispatchCompileError),
}

pub(crate) fn pattern_dispatch_from_matcher(matcher: &Matcher) -> Result<PatternDispatchPlan, PatternDispatchError> {
    let mut producer = PatternDispatchProducer::new(matcher);
    producer.walk(matcher.root, Vec::new())?;
    let subjects = producer.subject_refs_by_id();
    let matrix = producer.builder.build().map_err(PatternDispatchError::MatrixBuild)?;
    let graph = compile_dispatch_matrix(&matrix, DispatchCompileOptions::closed())
        .map_err(PatternDispatchError::Compile)?
        .graph;
    Ok(PatternDispatchPlan {
        matrix,
        graph,
        inputs: matcher.inputs.clone(),
        subjects,
        outcomes: producer.outcomes,
        guards: producer.guards,
        pinned: matcher.pinned.clone(),
        prepared_keys: matcher.prepared_keys.clone(),
        bitstring_direct_bindings: producer.bitstring_direct_bindings,
    })
}

pub(crate) fn matcher_from_pattern_dispatch_plan(plan: &PatternDispatchPlan) -> Result<Matcher, PatternDispatchError> {
    let mut builder = PatternMatcherBuilder {
        plan,
        nodes: Vec::new(),
        cache: HashMap::new(),
    };
    let root = builder.node(plan.graph.root)?;
    Ok(Matcher {
        inputs: plan.inputs.clone(),
        pinned: plan.pinned.clone(),
        prepared_keys: plan.prepared_keys.clone(),
        nodes: builder.nodes,
        root,
    })
}

struct PatternDispatchProducer<'a> {
    matcher: &'a Matcher,
    builder: DispatchMatrixBuilder,
    subjects: HashMap<SubjectRef, SubjectId>,
    guard_subject: SubjectId,
    outcomes: Vec<PatternDispatchOutcome>,
    guards: Vec<GuardExpr>,
    bitstring_direct_bindings: HashMap<SubjectId, Vec<String>>,
}

impl<'a> PatternDispatchProducer<'a> {
    fn new(matcher: &'a Matcher) -> Self {
        let mut builder = DispatchMatrixBuilder::new(super::Order::Source);
        let mut subjects = HashMap::new();
        for (ordinal, _) in matcher.inputs.iter().enumerate() {
            subjects.insert(SubjectRef::Input(InputId(ordinal as u32)), builder.add_input_subject());
        }
        let guard_subject = subjects
            .get(&SubjectRef::Input(InputId(0)))
            .copied()
            .unwrap_or_else(|| builder.add_input_subject());
        Self {
            matcher,
            builder,
            subjects,
            guard_subject,
            outcomes: Vec::new(),
            guards: Vec::new(),
            bitstring_direct_bindings: HashMap::new(),
        }
    }

    fn walk(&mut self, node: NodeId, path: Vec<RegionQuestion>) -> Result<(), PatternDispatchError> {
        let Some(node) = self.matcher.node(node) else {
            return Err(PatternDispatchError::UnknownMatcherNode(node));
        };
        match node {
            MatcherNode::Fail { .. } => Ok(()),
            MatcherNode::Leaf(leaf) => {
                let outcome = self.builder.add_outcome(OutcomeMultiplicity::Unique);
                let bindings = self.pattern_bindings(&leaf.bindings)?;
                self.builder
                    .add_arm_questions(path, EdgeEvidence::empty(), outcome)
                    .map_err(PatternDispatchError::MatrixBuild)?;
                self.outcomes.push(PatternDispatchOutcome {
                    outcome,
                    body_id: leaf.body_id,
                    bindings,
                    matcher_bindings: leaf.bindings.clone(),
                });
                Ok(())
            }
            MatcherNode::Test {
                test,
                on_true,
                on_false,
                ..
            } => {
                let mut true_path = path.clone();
                true_path.push(self.question_for_test(test)?);
                self.walk(*on_true, true_path)?;
                self.walk(*on_false, path)
            }
            MatcherNode::Guard {
                expr,
                on_true,
                on_false,
                ..
            } => {
                let guard = GuardId(self.guards.len() as u32);
                self.guards.push(expr.clone());
                let mut true_path = path.clone();
                true_path.push(RegionQuestion::new(RegionPredicate::new(
                    self.guard_subject,
                    Region::Guard(guard),
                )));
                self.walk(*on_true, true_path)?;
                self.walk(*on_false, path)
            }
            MatcherNode::Switch {
                subject,
                kind,
                cases,
                default,
                ..
            } => {
                for (key, case) in cases {
                    let mut case_path = path.clone();
                    case_path.push(self.question_for_switch(subject, kind, key)?);
                    self.walk(*case, case_path)?;
                }
                self.walk(*default, path)
            }
        }
    }

    fn pattern_bindings(
        &mut self,
        bindings: &[MatcherBinding],
    ) -> Result<Vec<PatternDispatchBinding>, PatternDispatchError> {
        bindings
            .iter()
            .map(|binding| {
                Ok(PatternDispatchBinding {
                    name: binding.name.clone(),
                    source: self.subject_id(&binding.source)?,
                })
            })
            .collect()
    }

    fn question_for_switch(
        &mut self,
        subject: &SubjectRef,
        kind: &SwitchKind,
        key: &SwitchKey,
    ) -> Result<RegionQuestion, PatternDispatchError> {
        match (kind, key) {
            (SwitchKind::TupleArity, SwitchKey::Arity(arity)) => {
                let subject = self.subject_id(subject)?;
                Ok(RegionQuestion::new(RegionPredicate::new(
                    subject,
                    Region::TupleArity(*arity),
                )))
            }
            (SwitchKind::Atom, SwitchKey::AtomName(name)) => {
                self.equality_question(subject, DispatchConst::AtomName(name.clone()))
            }
            (SwitchKind::Int, SwitchKey::Int(value)) => self.equality_question(subject, DispatchConst::Int(*value)),
            (SwitchKind::Float, SwitchKey::FloatBits(bits)) => {
                self.equality_question(subject, DispatchConst::FloatBits(*bits))
            }
            (SwitchKind::Bool, SwitchKey::Bool(value)) => self.equality_question(subject, DispatchConst::Bool(*value)),
            (SwitchKind::Nil, SwitchKey::Nil) | (SwitchKind::ListCons, SwitchKey::Nil) => {
                self.equality_question(subject, DispatchConst::Nil)
            }
            (SwitchKind::Binary, SwitchKey::Utf8Binary(bytes)) => {
                self.equality_question(subject, DispatchConst::Utf8Binary(bytes.clone()))
            }
            (SwitchKind::ListCons, SwitchKey::EmptyList) => {
                let subject = self.subject_id(subject)?;
                Ok(RegionQuestion::list_empty(subject))
            }
            (SwitchKind::ListCons, SwitchKey::Cons) => self.list_cons_question(subject),
            _ => Err(PatternDispatchError::UnsupportedSwitchCase {
                kind: kind.clone(),
                key: key.clone(),
            }),
        }
    }

    fn question_for_test(&mut self, test: &MatcherTest) -> Result<RegionQuestion, PatternDispatchError> {
        match test {
            MatcherTest::EqConst { subject, value } => {
                if matches!(value, MatcherConst::EmptyList) {
                    let subject = self.subject_id(subject)?;
                    Ok(RegionQuestion::list_empty(subject))
                } else {
                    let value = self.dispatch_const(value)?;
                    self.equality_question(subject, value)
                }
            }
            MatcherTest::EqPinned { subject, pinned } => {
                let subject = self.subject_id(subject)?;
                Ok(RegionQuestion::equality(
                    subject,
                    ComparisonValue::Pinned(PinnedValueId(pinned.0)),
                ))
            }
            MatcherTest::TupleArity { subject, arity } => {
                let subject = self.subject_id(subject)?;
                Ok(RegionQuestion::new(RegionPredicate::new(
                    subject,
                    Region::TupleArity(*arity),
                )))
            }
            MatcherTest::ListCons { subject } => self.list_cons_question(subject),
            MatcherTest::MapKind { subject } => {
                let subject = self.subject_id(subject)?;
                Ok(RegionQuestion::new(RegionPredicate::new(subject, Region::MapKind)))
            }
            MatcherTest::MapHasKey { subject, key } => {
                let map_subject = self.subject_id(subject)?;
                let dispatch_key = self.dispatch_const(key)?;
                let value = self.subject_id(&SubjectRef::MapValue {
                    map: Box::new(subject.clone()),
                    key: key.clone(),
                })?;
                Ok(RegionQuestion::map_key_present(map_subject, dispatch_key, value))
            }
            MatcherTest::Bitstring { subject, fields } => self.bitstring_question(subject, fields),
            MatcherTest::Type { subject, ty } => {
                let subject = self.subject_id(subject)?;
                Ok(RegionQuestion::type_region(subject, ty.clone()))
            }
        }
    }

    fn equality_question(
        &mut self,
        subject: &SubjectRef,
        value: DispatchConst,
    ) -> Result<RegionQuestion, PatternDispatchError> {
        let subject = self.subject_id(subject)?;
        Ok(RegionQuestion::equality(subject, ComparisonValue::Const(value)))
    }

    fn list_cons_question(&mut self, subject: &SubjectRef) -> Result<RegionQuestion, PatternDispatchError> {
        let subject_id = self.subject_id(subject)?;
        let head = self.subject_id(&SubjectRef::ListHead(Box::new(subject.clone())))?;
        let tail = self.subject_id(&SubjectRef::ListTail(Box::new(subject.clone())))?;
        Ok(RegionQuestion::list_cons(subject_id, head, tail))
    }

    fn bitstring_question(
        &mut self,
        subject: &SubjectRef,
        fields: &[MatcherBitField],
    ) -> Result<RegionQuestion, PatternDispatchError> {
        let subject_id = self.subject_id(subject)?;
        let mut binding_subjects = HashMap::new();
        let mut projections = Vec::new();
        let mut shapes = Vec::new();
        for (index, field) in fields.iter().enumerate() {
            let size = match &field.size {
                None => None,
                Some(MatcherBitSize::Literal(value)) => Some(BitstringFieldSize::Literal(*value)),
                Some(MatcherBitSize::BindingName(name)) => Some(
                    binding_subjects
                        .get(name)
                        .copied()
                        .map(BitstringFieldSize::Binding)
                        .unwrap_or_else(|| BitstringFieldSize::BindingName(name.clone())),
                ),
            };
            let field_subject = self.subject_id(&SubjectRef::BitstringField {
                bitstring: Box::new(subject.clone()),
                index: index as u32,
            })?;
            projections.push(EdgeProjection {
                source: subject_id,
                kind: ProjectionKind::BitstringField(index as u32),
                result: field_subject,
            });
            for name in &field.direct_bindings {
                binding_subjects.insert(name.clone(), field_subject);
            }
            self.bitstring_direct_bindings
                .insert(field_subject, field.direct_bindings.clone());
            shapes.push(BitstringFieldShape {
                kind: bitstring_field_kind(field.ty),
                size,
                endian: bitstring_endian(field.endian),
                signed: field.signed,
                unit: field.unit,
            });
        }
        let predicate = RegionPredicate::new(
            subject_id,
            Region::Bitstring(BitstringShape {
                fields: shapes,
                require_done: true,
            }),
        );
        let mut match_evidence = EdgeEvidence::from_proof(predicate.clone(), super::ProofSense::Holds);
        match_evidence.projections = projections;
        Ok(RegionQuestion {
            predicate: predicate.clone(),
            match_evidence,
            miss_evidence: EdgeEvidence::from_proof(predicate, super::ProofSense::DoesNotHold),
        })
    }

    fn subject_id(&mut self, subject: &SubjectRef) -> Result<SubjectId, PatternDispatchError> {
        if let Some(id) = self.subjects.get(subject).copied() {
            return Ok(id);
        }
        let id = match subject {
            SubjectRef::Input(input) => return Err(PatternDispatchError::UnknownInput(*input)),
            SubjectRef::TupleField { tuple, index } => {
                let source = self.subject_id(tuple)?;
                self.builder
                    .add_projected_subject(source, ProjectionKind::TupleField(*index))
                    .map_err(PatternDispatchError::MatrixBuild)?
            }
            SubjectRef::ListHead(list) => {
                let source = self.subject_id(list)?;
                self.builder
                    .add_projected_subject(source, ProjectionKind::ListHead)
                    .map_err(PatternDispatchError::MatrixBuild)?
            }
            SubjectRef::ListTail(list) => {
                let source = self.subject_id(list)?;
                self.builder
                    .add_projected_subject(source, ProjectionKind::ListTail)
                    .map_err(PatternDispatchError::MatrixBuild)?
            }
            SubjectRef::MapValue { map, key } => {
                let source = self.subject_id(map)?;
                let key = self.dispatch_const(key)?;
                self.builder
                    .add_projected_subject(source, ProjectionKind::MapValue { key })
                    .map_err(PatternDispatchError::MatrixBuild)?
            }
            SubjectRef::BitstringField { bitstring, index } => {
                let source = self.subject_id(bitstring)?;
                self.builder
                    .add_projected_subject(source, ProjectionKind::BitstringField(*index))
                    .map_err(PatternDispatchError::MatrixBuild)?
            }
        };
        self.subjects.insert(subject.clone(), id);
        Ok(id)
    }

    fn dispatch_const(&self, value: &MatcherConst) -> Result<DispatchConst, PatternDispatchError> {
        Ok(match value {
            MatcherConst::Int(value) => DispatchConst::Int(*value),
            MatcherConst::FloatBits(bits) => DispatchConst::FloatBits(*bits),
            MatcherConst::AtomName(name) => DispatchConst::AtomName(name.clone()),
            MatcherConst::Bool(value) => DispatchConst::Bool(*value),
            MatcherConst::Nil => DispatchConst::Nil,
            MatcherConst::EmptyList => DispatchConst::EmptyList,
            MatcherConst::Utf8Binary(bytes) => DispatchConst::Utf8Binary(bytes.clone()),
            MatcherConst::PreparedKey(index) => {
                let Some(prepared) = self.matcher.prepared_keys.get(*index as usize) else {
                    return Err(PatternDispatchError::UnknownPreparedKey(*index));
                };
                self.dispatch_const(prepared)?
            }
        })
    }

    fn subject_refs_by_id(&self) -> Vec<Option<SubjectRef>> {
        let max_subject = self
            .subjects
            .values()
            .map(|id| id.0)
            .chain(std::iter::once(self.guard_subject.0))
            .max()
            .unwrap_or(0);
        let mut out = vec![None; max_subject as usize + 1];
        for (subject, id) in &self.subjects {
            out[id.0 as usize] = Some(subject.clone());
        }
        out
    }
}

struct PatternMatcherBuilder<'a> {
    plan: &'a PatternDispatchPlan,
    nodes: Vec<MatcherNode>,
    cache: HashMap<GraphNodeId, NodeId>,
}

impl PatternMatcherBuilder<'_> {
    fn node(&mut self, graph_node: GraphNodeId) -> Result<NodeId, PatternDispatchError> {
        if let Some(node) = self.cache.get(&graph_node).copied() {
            return Ok(node);
        }
        let Some(dispatch_node) = self.plan.graph.node(graph_node).cloned() else {
            return Err(PatternDispatchError::UnknownGraphNode(graph_node));
        };
        let matcher_node = match dispatch_node {
            DispatchNode::Fail => MatcherNode::Fail {
                span: crate::diag::Span::DUMMY,
            },
            DispatchNode::Outcome { outcome, .. } => {
                let outcome = self
                    .plan
                    .outcomes
                    .iter()
                    .find(|entry| entry.outcome == outcome)
                    .ok_or(PatternDispatchError::UnknownOutcome(outcome))?;
                MatcherNode::Leaf(MatcherLeaf {
                    body_id: outcome.body_id,
                    bindings: outcome.matcher_bindings.clone(),
                    span: crate::diag::Span::DUMMY,
                })
            }
            DispatchNode::Test {
                predicate,
                on_match,
                on_miss,
            } => {
                let on_true = self.node(on_match.target)?;
                let on_false = self.node(on_miss.target)?;
                if let Region::Guard(guard) = predicate.region {
                    let expr = self
                        .plan
                        .guards
                        .get(guard.0 as usize)
                        .cloned()
                        .ok_or(PatternDispatchError::UnknownGuard(guard))?;
                    MatcherNode::Guard {
                        expr,
                        on_true,
                        on_false,
                        span: crate::diag::Span::DUMMY,
                    }
                } else {
                    MatcherNode::Test {
                        test: self.matcher_test(predicate.subject, &predicate.region, &on_match.evidence)?,
                        on_true,
                        on_false,
                        span: crate::diag::Span::DUMMY,
                    }
                }
            }
        };
        let id = NodeId(self.nodes.len() as u32);
        self.nodes.push(matcher_node);
        self.cache.insert(graph_node, id);
        Ok(id)
    }

    fn matcher_test(
        &self,
        subject: SubjectId,
        region: &Region,
        evidence: &EdgeEvidence,
    ) -> Result<MatcherTest, PatternDispatchError> {
        let subject_ref = self.matcher_subject(subject)?;
        Ok(match region {
            Region::Type(ty) => MatcherTest::Type {
                subject: subject_ref,
                ty: ty.clone(),
            },
            Region::Equal(ComparisonValue::Const(value)) => MatcherTest::EqConst {
                subject: subject_ref,
                value: matcher_const(value),
            },
            Region::Equal(ComparisonValue::Pinned(pinned)) => MatcherTest::EqPinned {
                subject: subject_ref,
                pinned: crate::exec::matcher::PinnedId(pinned.0),
            },
            Region::TupleArity(arity) => MatcherTest::TupleArity {
                subject: subject_ref,
                arity: *arity,
            },
            Region::List(super::ListRegion::Empty) => MatcherTest::EqConst {
                subject: subject_ref,
                value: MatcherConst::EmptyList,
            },
            Region::List(super::ListRegion::Cons) => MatcherTest::ListCons { subject: subject_ref },
            Region::MapKind => MatcherTest::MapKind { subject: subject_ref },
            Region::MapKeyPresent { key } => MatcherTest::MapHasKey {
                subject: subject_ref,
                key: self.matcher_map_key(subject, key, evidence),
            },
            Region::Bitstring(shape) => MatcherTest::Bitstring {
                subject: subject_ref,
                fields: self.matcher_bitstring_fields(subject, shape)?,
            },
            other => return Err(PatternDispatchError::UnsupportedRegion(other.clone())),
        })
    }

    fn matcher_subject(&self, subject: SubjectId) -> Result<SubjectRef, PatternDispatchError> {
        self.plan
            .subjects
            .get(subject.0 as usize)
            .and_then(|subject| subject.clone())
            .ok_or(PatternDispatchError::UnknownSubject(subject))
    }

    fn matcher_map_key(&self, map_subject: SubjectId, key: &DispatchConst, evidence: &EdgeEvidence) -> MatcherConst {
        evidence
            .projections
            .iter()
            .find_map(|projection| {
                if projection.source != map_subject {
                    return None;
                }
                let ProjectionKind::MapValue { .. } = &projection.kind else {
                    return None;
                };
                match self.plan.subjects.get(projection.result.0 as usize) {
                    Some(Some(SubjectRef::MapValue { key, .. })) => Some(key.clone()),
                    _ => None,
                }
            })
            .unwrap_or_else(|| matcher_const(key))
    }

    fn matcher_bitstring_fields(
        &self,
        bitstring: SubjectId,
        shape: &BitstringShape,
    ) -> Result<Vec<MatcherBitField>, PatternDispatchError> {
        shape
            .fields
            .iter()
            .enumerate()
            .map(|(index, field)| {
                let field_subject = self
                    .projected_subject(bitstring, ProjectionKind::BitstringField(index as u32))
                    .ok_or(PatternDispatchError::UnknownSubject(SubjectId(u32::MAX)))?;
                Ok(MatcherBitField {
                    ty: matcher_bit_type(field.kind),
                    size: self.matcher_bit_size(&field.size)?,
                    endian: matcher_endian(field.endian),
                    signed: field.signed,
                    unit: field.unit,
                    direct_bindings: self
                        .plan
                        .bitstring_direct_bindings
                        .get(&field_subject)
                        .cloned()
                        .unwrap_or_default(),
                })
            })
            .collect()
    }

    fn matcher_bit_size(
        &self,
        size: &Option<BitstringFieldSize>,
    ) -> Result<Option<MatcherBitSize>, PatternDispatchError> {
        Ok(match size {
            None => None,
            Some(BitstringFieldSize::Literal(value)) => Some(MatcherBitSize::Literal(*value)),
            Some(BitstringFieldSize::BindingName(name)) => Some(MatcherBitSize::BindingName(name.clone())),
            Some(BitstringFieldSize::Binding(subject)) => {
                let names = self
                    .plan
                    .bitstring_direct_bindings
                    .get(subject)
                    .ok_or(PatternDispatchError::MissingBitstringBindingName(*subject))?;
                Some(MatcherBitSize::BindingName(
                    names
                        .first()
                        .cloned()
                        .ok_or(PatternDispatchError::MissingBitstringBindingName(*subject))?,
                ))
            }
        })
    }

    fn projected_subject(&self, source: SubjectId, kind: ProjectionKind) -> Option<SubjectId> {
        self.plan
            .matrix
            .subjects
            .iter()
            .find_map(|subject| match &subject.source {
                super::SubjectSource::Projection(projection)
                    if projection.source == source && projection.kind == kind =>
                {
                    Some(subject.id)
                }
                _ => None,
            })
    }
}

fn bitstring_field_kind(kind: MatcherBitType) -> BitstringFieldKind {
    match kind {
        MatcherBitType::Integer => BitstringFieldKind::Integer,
        MatcherBitType::Float => BitstringFieldKind::Float,
        MatcherBitType::Binary => BitstringFieldKind::Binary,
        MatcherBitType::Bits => BitstringFieldKind::Bits,
        MatcherBitType::Utf8 => BitstringFieldKind::Utf8,
        MatcherBitType::Utf16 => BitstringFieldKind::Utf16,
        MatcherBitType::Utf32 => BitstringFieldKind::Utf32,
    }
}

fn bitstring_endian(endian: MatcherEndian) -> BitstringEndian {
    match endian {
        MatcherEndian::Big => BitstringEndian::Big,
        MatcherEndian::Little => BitstringEndian::Little,
        MatcherEndian::Native => BitstringEndian::Native,
    }
}

fn matcher_const(value: &DispatchConst) -> MatcherConst {
    match value {
        DispatchConst::Int(value) => MatcherConst::Int(*value),
        DispatchConst::FloatBits(bits) => MatcherConst::FloatBits(*bits),
        DispatchConst::AtomName(name) => MatcherConst::AtomName(name.clone()),
        DispatchConst::Bool(value) => MatcherConst::Bool(*value),
        DispatchConst::Nil => MatcherConst::Nil,
        DispatchConst::EmptyList => MatcherConst::EmptyList,
        DispatchConst::Utf8Binary(bytes) => MatcherConst::Utf8Binary(bytes.clone()),
    }
}

fn matcher_bit_type(kind: BitstringFieldKind) -> MatcherBitType {
    match kind {
        BitstringFieldKind::Integer => MatcherBitType::Integer,
        BitstringFieldKind::Float => MatcherBitType::Float,
        BitstringFieldKind::Binary => MatcherBitType::Binary,
        BitstringFieldKind::Bits => MatcherBitType::Bits,
        BitstringFieldKind::Utf8 => MatcherBitType::Utf8,
        BitstringFieldKind::Utf16 => MatcherBitType::Utf16,
        BitstringFieldKind::Utf32 => MatcherBitType::Utf32,
    }
}

fn matcher_endian(endian: BitstringEndian) -> MatcherEndian {
    match endian {
        BitstringEndian::Big => MatcherEndian::Big,
        BitstringEndian::Little => MatcherEndian::Little,
        BitstringEndian::Native => MatcherEndian::Native,
    }
}
