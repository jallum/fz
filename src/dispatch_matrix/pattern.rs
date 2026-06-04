use super::{
    BitstringEndian, BitstringFieldKind, BitstringFieldShape, BitstringFieldSize, BitstringShape, ComparisonValue,
    DispatchCompileError, DispatchCompileOptions, DispatchConst, DispatchGraph, DispatchMatrix, DispatchMatrixBuilder,
    DispatchMatrixError, EdgeEvidence, EdgeProjection, GuardId, OutcomeId, OutcomeMultiplicity, PinnedValueId,
    ProjectionKind, Region, RegionPredicate, RegionQuestion, SubjectId, compile_dispatch_matrix,
};
use crate::exec::matcher::{
    GuardExpr, InputId, Matcher, MatcherBinding, MatcherBitField, MatcherBitSize, MatcherBitType, MatcherConst,
    MatcherEndian, MatcherNode, MatcherTest, NodeId, PinnedInput, SubjectRef, SwitchKey, SwitchKind,
};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternDispatchPlan {
    pub(crate) matrix: DispatchMatrix,
    pub(crate) graph: DispatchGraph,
    pub(crate) outcomes: Vec<PatternDispatchOutcome>,
    pub(crate) guards: Vec<GuardExpr>,
    pub(crate) pinned: Vec<PinnedInput>,
    pub(crate) prepared_keys: Vec<MatcherConst>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternDispatchOutcome {
    pub(crate) outcome: OutcomeId,
    pub(crate) body_id: u32,
    pub(crate) bindings: Vec<PatternDispatchBinding>,
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
    UnsupportedSwitchCase { kind: SwitchKind, key: SwitchKey },
    MatrixBuild(DispatchMatrixError),
    Compile(DispatchCompileError),
}

pub(crate) fn pattern_dispatch_from_matcher(matcher: &Matcher) -> Result<PatternDispatchPlan, PatternDispatchError> {
    let mut producer = PatternDispatchProducer::new(matcher);
    producer.walk(matcher.root, Vec::new())?;
    let matrix = producer.builder.build().map_err(PatternDispatchError::MatrixBuild)?;
    let graph = compile_dispatch_matrix(&matrix, DispatchCompileOptions::closed())
        .map_err(PatternDispatchError::Compile)?
        .graph;
    Ok(PatternDispatchPlan {
        matrix,
        graph,
        outcomes: producer.outcomes,
        guards: producer.guards,
        pinned: matcher.pinned.clone(),
        prepared_keys: matcher.prepared_keys.clone(),
    })
}

struct PatternDispatchProducer<'a> {
    matcher: &'a Matcher,
    builder: DispatchMatrixBuilder,
    subjects: HashMap<SubjectRef, SubjectId>,
    guard_subject: SubjectId,
    outcomes: Vec<PatternDispatchOutcome>,
    guards: Vec<GuardExpr>,
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
