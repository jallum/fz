use self::source::{collect_pinned_names, direct_bitfield_bindings};
use super::{
    BitstringEndian, BitstringFieldKind, BitstringFieldShape, BitstringFieldSize, BitstringShape, ComparisonValue,
    DispatchCompileError, DispatchCompileOptions, DispatchConst, DispatchGraph, DispatchMatrix, DispatchMatrixBuilder,
    DispatchMatrixError, EdgeEvidence, EdgeProjection, GuardId, OutcomeId, OutcomeMultiplicity, PinnedValueId,
    ProjectionKind, Region, RegionPredicate, RegionQuestion, SubjectId, compile_dispatch_matrix,
};
use crate::ast::{BitSize, BitType, Endian, Expr, Pattern, Spanned};
use crate::diag::{FileId, Span};
use crate::fz_ir::Var;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

pub(crate) mod source;
pub(crate) use source::{
    KnownSubjectDomain, PatternBodyId, PatternRow, SourcePatternError, SourcePatternRows, collect_guard_capture_names,
    find_unreachable_rows, is_inexhaustive_with_domains,
};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PatternDispatchPlan {
    pub(crate) matrix: DispatchMatrix,
    pub(crate) graph: DispatchGraph,
    pub(crate) inputs: Vec<PatternInput>,
    pub(crate) subjects: Vec<Option<PatternSubjectRef>>,
    pub(crate) outcomes: Vec<PatternDispatchOutcome>,
    pub(crate) guards: Vec<PatternGuardExpr>,
    pub(crate) pinned: Vec<PatternPinnedInput>,
    pub(crate) prepared_keys: Vec<DispatchConst>,
    pub(crate) bitstring_direct_bindings: HashMap<SubjectId, Vec<String>>,
}

impl PatternDispatchPlan {
    pub(crate) fn outcome(&self, id: OutcomeId) -> Option<&PatternDispatchOutcome> {
        self.outcomes.iter().find(|entry| entry.outcome == id)
    }

    pub(crate) fn subject_ref(&self, id: SubjectId) -> Option<&PatternSubjectRef> {
        self.subjects.get(id.0 as usize).and_then(|entry| entry.as_ref())
    }

    pub(crate) fn remap_file_ids(&mut self, remap: &HashMap<FileId, FileId>) {
        for input in &mut self.inputs {
            remap_span(&mut input.span, remap);
        }
        for pinned in &mut self.pinned {
            remap_span(&mut pinned.span, remap);
        }
        for guard in &mut self.guards {
            guard.remap_file_ids(remap);
        }
        for outcome in &mut self.outcomes {
            remap_span(&mut outcome.span, remap);
            for binding in &mut outcome.bindings {
                remap_span(&mut binding.span, remap);
            }
        }
    }

    pub(crate) fn visit_spans(&self, f: &mut impl FnMut(Span)) {
        for input in &self.inputs {
            f(input.span);
        }
        for pinned in &self.pinned {
            f(pinned.span);
        }
        for guard in &self.guards {
            guard.visit_spans(f);
        }
        for outcome in &self.outcomes {
            f(outcome.span);
            for binding in &outcome.bindings {
                f(binding.span);
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PatternInput {
    pub(crate) var: Option<Var>,
    pub(crate) span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PatternPinnedInput {
    pub(crate) name: String,
    pub(crate) var: Option<Var>,
    pub(crate) span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PatternDispatchOutcome {
    pub(crate) outcome: OutcomeId,
    pub(crate) body_id: PatternBodyId,
    pub(crate) bindings: Vec<PatternDispatchBinding>,
    pub(crate) span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PatternDispatchBinding {
    pub(crate) name: String,
    pub(crate) source: SubjectId,
    pub(crate) span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum PatternSubjectRef {
    Input(u32),
    TupleField {
        tuple: Box<PatternSubjectRef>,
        index: u32,
    },
    ListHead(Box<PatternSubjectRef>),
    ListTail(Box<PatternSubjectRef>),
    MapValue {
        map: Box<PatternSubjectRef>,
        key: DispatchConst,
    },
    BitstringField {
        bitstring: Box<PatternSubjectRef>,
        index: u32,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum PatternGuardExpr {
    Const(DispatchConst),
    Subject(SubjectId),
    Pinned(PinnedValueId),
    Unary {
        op: PatternGuardUnaryOp,
        expr: Box<PatternGuardExpr>,
    },
    Binary {
        op: PatternGuardBinOp,
        lhs: Box<PatternGuardExpr>,
        rhs: Box<PatternGuardExpr>,
    },
    Dispatch {
        inputs: Vec<PatternGuardExpr>,
        dispatch: Box<PatternGuardDispatch>,
    },
}

impl PatternGuardExpr {
    fn remap_file_ids(&mut self, remap: &HashMap<FileId, FileId>) {
        match self {
            PatternGuardExpr::Unary { expr, .. } => expr.remap_file_ids(remap),
            PatternGuardExpr::Binary { lhs, rhs, .. } => {
                lhs.remap_file_ids(remap);
                rhs.remap_file_ids(remap);
            }
            PatternGuardExpr::Dispatch { inputs, dispatch } => {
                for input in inputs {
                    input.remap_file_ids(remap);
                }
                dispatch.plan.remap_file_ids(remap);
                for body in &mut dispatch.bodies {
                    body.remap_file_ids(remap);
                }
            }
            PatternGuardExpr::Const(_) | PatternGuardExpr::Subject(_) | PatternGuardExpr::Pinned(_) => {}
        }
    }

    fn visit_spans(&self, f: &mut impl FnMut(Span)) {
        match self {
            PatternGuardExpr::Unary { expr, .. } => expr.visit_spans(f),
            PatternGuardExpr::Binary { lhs, rhs, .. } => {
                lhs.visit_spans(f);
                rhs.visit_spans(f);
            }
            PatternGuardExpr::Dispatch { inputs, dispatch } => {
                for input in inputs {
                    input.visit_spans(f);
                }
                dispatch.plan.visit_spans(f);
                for body in &dispatch.bodies {
                    body.visit_spans(f);
                }
            }
            PatternGuardExpr::Const(_) | PatternGuardExpr::Subject(_) | PatternGuardExpr::Pinned(_) => {}
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PatternGuardDispatch {
    pub(crate) plan: Box<PatternDispatchPlan>,
    pub(crate) bodies: Vec<PatternGuardExpr>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum PatternGuardUnaryOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum PatternGuardBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Neq,
    Lt,
    LtEq,
    Gt,
    GtEq,
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PatternDispatchError {
    SourcePattern(SourcePatternError),
    MatrixBuild(DispatchMatrixError),
    Compile(DispatchCompileError),
}

pub(crate) fn prepared_key_name(index: usize) -> String {
    format!("__dispatch_key_{}", index)
}

pub(crate) fn guard_expr_from_ast<F>(
    expr: &Expr,
    bindings: &HashMap<String, SubjectId>,
    pinned_by_name: &HashMap<String, PinnedValueId>,
    guard_call_resolver: &mut F,
) -> Result<PatternGuardExpr, SourcePatternError>
where
    F: FnMut(&str, usize, Vec<PatternGuardExpr>) -> Result<Option<PatternGuardExpr>, SourcePatternError>,
{
    Ok(match expr {
        Expr::Int(value) => PatternGuardExpr::Const(DispatchConst::Int(*value)),
        Expr::Float(value) => PatternGuardExpr::Const(DispatchConst::FloatBits(value.to_bits())),
        Expr::Binary(bytes) => PatternGuardExpr::Const(DispatchConst::Utf8Binary(bytes.clone())),
        Expr::Atom(name) => PatternGuardExpr::Const(DispatchConst::AtomName(name.clone())),
        Expr::Bool(value) => PatternGuardExpr::Const(DispatchConst::Bool(*value)),
        Expr::Nil => PatternGuardExpr::Const(DispatchConst::Nil),
        Expr::Var(name) => {
            if let Some(subject) = bindings.get(name) {
                PatternGuardExpr::Subject(*subject)
            } else if let Some(pinned) = pinned_by_name.get(name) {
                PatternGuardExpr::Pinned(*pinned)
            } else {
                return Err(SourcePatternError::UnknownGuardVar(name.clone()));
            }
        }
        Expr::Ascribe(inner, _) => guard_expr_from_ast(&inner.node, bindings, pinned_by_name, guard_call_resolver)?,
        Expr::UnOp(crate::ast::UnOp::Not, arg) => PatternGuardExpr::Unary {
            op: PatternGuardUnaryOp::Not,
            expr: Box::new(guard_expr_from_ast(
                &arg.node,
                bindings,
                pinned_by_name,
                guard_call_resolver,
            )?),
        },
        Expr::UnOp(crate::ast::UnOp::Neg, arg) => PatternGuardExpr::Unary {
            op: PatternGuardUnaryOp::Neg,
            expr: Box::new(guard_expr_from_ast(
                &arg.node,
                bindings,
                pinned_by_name,
                guard_call_resolver,
            )?),
        },
        Expr::BinOp(op, lhs, rhs) => PatternGuardExpr::Binary {
            op: match op {
                crate::ast::BinOp::Add => PatternGuardBinOp::Add,
                crate::ast::BinOp::Sub => PatternGuardBinOp::Sub,
                crate::ast::BinOp::Mul => PatternGuardBinOp::Mul,
                crate::ast::BinOp::Div => PatternGuardBinOp::Div,
                crate::ast::BinOp::Rem => PatternGuardBinOp::Rem,
                crate::ast::BinOp::Eq => PatternGuardBinOp::Eq,
                crate::ast::BinOp::Neq => PatternGuardBinOp::Neq,
                crate::ast::BinOp::Lt => PatternGuardBinOp::Lt,
                crate::ast::BinOp::LtEq => PatternGuardBinOp::LtEq,
                crate::ast::BinOp::Gt => PatternGuardBinOp::Gt,
                crate::ast::BinOp::GtEq => PatternGuardBinOp::GtEq,
                crate::ast::BinOp::And => PatternGuardBinOp::And,
                crate::ast::BinOp::Or => PatternGuardBinOp::Or,
                crate::ast::BinOp::Pipe
                | crate::ast::BinOp::Cons
                | crate::ast::BinOp::ListConcat
                | crate::ast::BinOp::ListSubtract
                | crate::ast::BinOp::BinConcat
                | crate::ast::BinOp::Range
                | crate::ast::BinOp::RangeStep
                | crate::ast::BinOp::In
                | crate::ast::BinOp::NotIn => return Err(SourcePatternError::UnsupportedGuardExpr),
            },
            lhs: Box::new(guard_expr_from_ast(
                &lhs.node,
                bindings,
                pinned_by_name,
                guard_call_resolver,
            )?),
            rhs: Box::new(guard_expr_from_ast(
                &rhs.node,
                bindings,
                pinned_by_name,
                guard_call_resolver,
            )?),
        },
        Expr::Call(target, args) => {
            let callee = match &target.node {
                Expr::Var(name) => Some((name.as_str(), args.len())),
                Expr::FnRef { name, arity } if *arity == args.len() => Some((name.as_str(), *arity)),
                _ => None,
            };
            let Some((name, arity)) = callee else {
                return Err(SourcePatternError::UnsupportedGuardExpr);
            };
            let args = args
                .iter()
                .map(|arg| guard_expr_from_ast(&arg.node, bindings, pinned_by_name, guard_call_resolver))
                .collect::<Result<Vec<_>, _>>()?;
            match guard_call_resolver(name, arity, args)? {
                Some(expr) => expr,
                None => return Err(SourcePatternError::UnsupportedGuardExpr),
            }
        }
        _ => return Err(SourcePatternError::UnsupportedGuardExpr),
    })
}

pub(crate) fn pattern_dispatch_from_source(
    patterns: SourcePatternRows,
) -> Result<PatternDispatchPlan, PatternDispatchError> {
    let mut resolver = |_name: &str,
                        _arity: usize,
                        _args: Vec<PatternGuardExpr>|
     -> Result<Option<PatternGuardExpr>, SourcePatternError> { Ok(None) };
    pattern_dispatch_from_source_with_guard_resolver(patterns, &mut resolver)
}

pub(crate) fn pattern_dispatch_from_source_with_guard_resolver<F>(
    patterns: SourcePatternRows,
    guard_call_resolver: &mut F,
) -> Result<PatternDispatchPlan, PatternDispatchError>
where
    F: FnMut(&str, usize, Vec<PatternGuardExpr>) -> Result<Option<PatternGuardExpr>, SourcePatternError>,
{
    let mut producer = PatternDispatchProducer::new(&patterns).map_err(PatternDispatchError::SourcePattern)?;
    producer
        .add_rows(patterns.rows, guard_call_resolver)
        .map_err(PatternDispatchError::SourcePattern)?;
    producer.finish()
}

struct PatternDispatchProducer {
    builder: DispatchMatrixBuilder,
    input_by_var: HashMap<Var, u32>,
    subjects: HashMap<PatternSubjectRef, SubjectId>,
    guard_subject: SubjectId,
    inputs: Vec<PatternInput>,
    pinned: Vec<PatternPinnedInput>,
    pinned_by_name: HashMap<String, PinnedValueId>,
    prepared_keys: Vec<DispatchConst>,
    outcomes: Vec<PatternDispatchOutcome>,
    guards: Vec<PatternGuardExpr>,
    bitstring_direct_bindings: HashMap<SubjectId, Vec<String>>,
}

impl PatternDispatchProducer {
    fn new(patterns: &SourcePatternRows) -> Result<Self, SourcePatternError> {
        validate_source_order(patterns)?;
        let mut builder = DispatchMatrixBuilder::new(super::Order::Source);
        let mut input_by_var = HashMap::new();
        let mut subjects = HashMap::new();
        let mut inputs = Vec::new();
        for (ordinal, var) in patterns.subjects.iter().copied().enumerate() {
            let subject = builder.add_input_subject();
            let ordinal = ordinal as u32;
            input_by_var.insert(var, ordinal);
            subjects.insert(PatternSubjectRef::Input(ordinal), subject);
            inputs.push(PatternInput {
                var: Some(var),
                span: Span::DUMMY,
            });
        }
        let guard_subject = subjects
            .get(&PatternSubjectRef::Input(0))
            .copied()
            .unwrap_or_else(|| builder.add_input_subject());
        let pinned_names = collect_pinned_names(patterns);
        let pinned = pinned_names
            .iter()
            .map(|name| PatternPinnedInput {
                name: name.clone(),
                var: None,
                span: Span::DUMMY,
            })
            .collect::<Vec<_>>();
        let pinned_by_name = pinned_names
            .into_iter()
            .enumerate()
            .map(|(index, name)| (name, PinnedValueId(index as u32)))
            .collect();
        Ok(Self {
            builder,
            input_by_var,
            subjects,
            guard_subject,
            inputs,
            pinned,
            pinned_by_name,
            prepared_keys: Vec::new(),
            outcomes: Vec::new(),
            guards: Vec::new(),
            bitstring_direct_bindings: HashMap::new(),
        })
    }

    fn add_rows<F>(&mut self, rows: Vec<PatternRow>, guard_call_resolver: &mut F) -> Result<(), SourcePatternError>
    where
        F: FnMut(&str, usize, Vec<PatternGuardExpr>) -> Result<Option<PatternGuardExpr>, SourcePatternError>,
    {
        for row in rows {
            self.add_row(row, guard_call_resolver)?;
        }
        Ok(())
    }

    fn add_row<F>(&mut self, row: PatternRow, guard_call_resolver: &mut F) -> Result<(), SourcePatternError>
    where
        F: FnMut(&str, usize, Vec<PatternGuardExpr>) -> Result<Option<PatternGuardExpr>, SourcePatternError>,
    {
        let mut questions = Vec::new();
        let mut bindings = Vec::new();
        for (pattern, var) in row.patterns.iter().zip(self.input_vars_for_row()) {
            let subject = PatternSubjectRef::Input(var);
            self.append_pattern(&pattern.node, pattern.span, &subject, &mut questions, &mut bindings)?;
        }
        for (var, ty) in &row.preconditions {
            let ordinal = *self
                .input_by_var
                .get(var)
                .ok_or(SourcePatternError::UnknownSubject(*var))?;
            let subject = self.subject_id(&PatternSubjectRef::Input(ordinal))?;
            questions.push(RegionQuestion::type_region(subject, ty.clone()));
        }
        if let Some(guard) = &row.guard {
            let mut bound = HashMap::new();
            for binding in &bindings {
                bound.insert(binding.name.clone(), binding.source);
            }
            let guard_expr = guard_expr_from_ast(&guard.node, &bound, &self.pinned_by_name, guard_call_resolver)?;
            let guard_id = GuardId(self.guards.len() as u32);
            self.guards.push(guard_expr);
            questions.push(RegionQuestion::new(RegionPredicate::new(
                self.guard_subject,
                Region::Guard(guard_id),
            )));
        }
        let outcome = self.builder.add_outcome(OutcomeMultiplicity::Unique);
        self.builder
            .add_arm_questions(questions, EdgeEvidence::empty(), outcome)
            .map_err(|err| SourcePatternError::DispatchMatrix(format!("{err:?}")))?;
        self.outcomes.push(PatternDispatchOutcome {
            outcome,
            body_id: row.body_id,
            bindings,
            span: row
                .patterns
                .first()
                .map(|pattern| pattern.span)
                .or_else(|| row.guard.as_ref().map(|guard| guard.span))
                .unwrap_or(Span::DUMMY),
        });
        Ok(())
    }

    fn input_vars_for_row(&self) -> Vec<u32> {
        (0..self.inputs.len() as u32).collect()
    }

    fn finish(self) -> Result<PatternDispatchPlan, PatternDispatchError> {
        let subjects = self.subject_refs_by_id();
        let matrix = self.builder.build().map_err(PatternDispatchError::MatrixBuild)?;
        let graph = compile_dispatch_matrix(&matrix, DispatchCompileOptions::closed())
            .map_err(PatternDispatchError::Compile)?
            .graph;
        Ok(PatternDispatchPlan {
            matrix,
            graph,
            inputs: self.inputs,
            subjects,
            outcomes: self.outcomes,
            guards: self.guards,
            pinned: self.pinned,
            prepared_keys: self.prepared_keys,
            bitstring_direct_bindings: self.bitstring_direct_bindings,
        })
    }

    fn append_pattern(
        &mut self,
        pattern: &Pattern,
        span: Span,
        subject: &PatternSubjectRef,
        questions: &mut Vec<RegionQuestion>,
        bindings: &mut Vec<PatternDispatchBinding>,
    ) -> Result<(), SourcePatternError> {
        match pattern {
            Pattern::Wildcard => {}
            Pattern::Var(name) => self.bind(name, span, subject, bindings)?,
            Pattern::As(name, inner) => {
                self.bind(name, span, subject, bindings)?;
                self.append_pattern(&inner.node, inner.span, subject, questions, bindings)?;
            }
            Pattern::Pinned(name) => {
                let pinned = *self
                    .pinned_by_name
                    .get(name)
                    .ok_or_else(|| SourcePatternError::UnknownPinned(name.clone()))?;
                let subject = self.subject_id(subject)?;
                questions.push(RegionQuestion::equality(subject, ComparisonValue::Pinned(pinned)));
            }
            Pattern::Int(value) => self.const_question(subject, DispatchConst::Int(*value), questions)?,
            Pattern::Float(value) => {
                self.const_question(subject, DispatchConst::FloatBits(value.to_bits()), questions)?
            }
            Pattern::Binary(bytes) => {
                self.const_question(subject, DispatchConst::Utf8Binary(bytes.clone()), questions)?
            }
            Pattern::Atom(name) => self.const_question(subject, DispatchConst::AtomName(name.clone()), questions)?,
            Pattern::Bool(value) => self.const_question(subject, DispatchConst::Bool(*value), questions)?,
            Pattern::Nil => self.const_question(subject, DispatchConst::Nil, questions)?,
            Pattern::Tuple(fields) => {
                let subject_id = self.subject_id(subject)?;
                let mut field_subjects = Vec::with_capacity(fields.len());
                for (index, field) in fields.iter().enumerate() {
                    let field_subject = PatternSubjectRef::TupleField {
                        tuple: Box::new(subject.clone()),
                        index: index as u32,
                    };
                    let field_id = self.subject_id(&field_subject)?;
                    field_subjects.push((field_subject, field_id, field));
                }
                questions.push(RegionQuestion::tuple_arity(
                    subject_id,
                    fields.len() as u32,
                    field_subjects.iter().map(|(_, field_id, _)| *field_id),
                ));
                for (field_subject, _, field) in field_subjects {
                    self.append_pattern(&field.node, field.span, &field_subject, questions, bindings)?;
                }
            }
            Pattern::List(elems, tail) => {
                self.append_list_pattern(elems, tail.as_deref(), subject, questions, bindings)?;
            }
            Pattern::Map(entries) => {
                let subject_id = self.subject_id(subject)?;
                questions.push(RegionQuestion::new(RegionPredicate::new(subject_id, Region::MapKind)));
                for (key_pat, val_pat) in entries {
                    let key = self.map_key(&key_pat.node)?;
                    self.prepare_heap_key(&key);
                    let value_subject = PatternSubjectRef::MapValue {
                        map: Box::new(subject.clone()),
                        key: key.clone(),
                    };
                    let value_id = self.subject_id(&value_subject)?;
                    questions.push(RegionQuestion::map_key_present(subject_id, key, value_id));
                    self.append_pattern(&val_pat.node, val_pat.span, &value_subject, questions, bindings)?;
                }
            }
            Pattern::Struct { fields, .. } => {
                for (_, value) in fields {
                    self.append_pattern(&value.node, value.span, subject, questions, bindings)?;
                }
            }
            Pattern::Bitstring(fields) => {
                let question = self.bitstring_question(subject, fields)?;
                questions.push(question);
                for (index, field) in fields.iter().enumerate() {
                    let field_subject = PatternSubjectRef::BitstringField {
                        bitstring: Box::new(subject.clone()),
                        index: index as u32,
                    };
                    self.append_pattern(&field.value.node, field.value.span, &field_subject, questions, bindings)?;
                }
            }
        }
        Ok(())
    }

    fn append_list_pattern(
        &mut self,
        elems: &[Spanned<Pattern>],
        tail: Option<&Spanned<Pattern>>,
        subject: &PatternSubjectRef,
        questions: &mut Vec<RegionQuestion>,
        bindings: &mut Vec<PatternDispatchBinding>,
    ) -> Result<(), SourcePatternError> {
        if elems.is_empty() {
            if let Some(tail) = tail {
                return self.append_pattern(&tail.node, tail.span, subject, questions, bindings);
            }
            let subject_id = self.subject_id(subject)?;
            questions.push(RegionQuestion::list_empty(subject_id));
            return Ok(());
        }
        let subject_id = self.subject_id(subject)?;
        let head_subject = PatternSubjectRef::ListHead(Box::new(subject.clone()));
        let tail_subject = PatternSubjectRef::ListTail(Box::new(subject.clone()));
        let head_id = self.subject_id(&head_subject)?;
        let tail_id = self.subject_id(&tail_subject)?;
        questions.push(RegionQuestion::list_cons(subject_id, head_id, tail_id));
        self.append_pattern(&elems[0].node, elems[0].span, &head_subject, questions, bindings)?;
        if elems.len() == 1 {
            if let Some(tail) = tail {
                self.append_pattern(&tail.node, tail.span, &tail_subject, questions, bindings)
            } else {
                questions.push(RegionQuestion::list_empty(tail_id));
                Ok(())
            }
        } else {
            self.append_list_pattern(&elems[1..], tail, &tail_subject, questions, bindings)
        }
    }

    fn bitstring_question(
        &mut self,
        subject: &PatternSubjectRef,
        fields: &[crate::ast::BitField<Spanned<Pattern>>],
    ) -> Result<RegionQuestion, SourcePatternError> {
        let subject_id = self.subject_id(subject)?;
        let mut binding_subjects = HashMap::new();
        let mut projections = Vec::new();
        let mut shapes = Vec::new();
        for (index, field) in fields.iter().enumerate() {
            let size = match &field.spec.size {
                None => None,
                Some(BitSize::Literal(value)) => Some(BitstringFieldSize::Literal(*value)),
                Some(BitSize::Var(name)) => Some(
                    binding_subjects
                        .get(name)
                        .copied()
                        .map(BitstringFieldSize::Binding)
                        .unwrap_or_else(|| BitstringFieldSize::BindingName(name.clone())),
                ),
            };
            let field_subject = PatternSubjectRef::BitstringField {
                bitstring: Box::new(subject.clone()),
                index: index as u32,
            };
            let field_id = self.subject_id(&field_subject)?;
            projections.push(EdgeProjection {
                source: subject_id,
                kind: ProjectionKind::BitstringField(index as u32),
                result: field_id,
            });
            let direct_bindings = direct_bitfield_bindings(&field.value.node);
            for name in &direct_bindings {
                binding_subjects.insert(name.clone(), field_id);
            }
            self.bitstring_direct_bindings.insert(field_id, direct_bindings);
            shapes.push(BitstringFieldShape {
                kind: bitstring_field_kind(field.spec.ty),
                size,
                endian: bitstring_endian(field.spec.endian),
                signed: field.spec.signed,
                unit: field.spec.unit,
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

    fn const_question(
        &mut self,
        subject: &PatternSubjectRef,
        value: DispatchConst,
        questions: &mut Vec<RegionQuestion>,
    ) -> Result<(), SourcePatternError> {
        let subject = self.subject_id(subject)?;
        questions.push(RegionQuestion::equality(subject, ComparisonValue::Const(value)));
        Ok(())
    }

    fn bind(
        &mut self,
        name: &str,
        span: Span,
        subject: &PatternSubjectRef,
        bindings: &mut Vec<PatternDispatchBinding>,
    ) -> Result<(), SourcePatternError> {
        let source = self.subject_id(subject)?;
        bindings.push(PatternDispatchBinding {
            name: name.to_string(),
            source,
            span,
        });
        Ok(())
    }

    fn subject_id(&mut self, subject: &PatternSubjectRef) -> Result<SubjectId, SourcePatternError> {
        if let Some(id) = self.subjects.get(subject).copied() {
            return Ok(id);
        }
        let id = match subject {
            PatternSubjectRef::Input(_) => return Err(SourcePatternError::UnknownSubject(Var(u32::MAX))),
            PatternSubjectRef::TupleField { tuple, index } => {
                let source = self.subject_id(tuple)?;
                self.builder
                    .add_projected_subject(source, ProjectionKind::TupleField(*index))
                    .map_err(|err| SourcePatternError::DispatchMatrix(format!("{err:?}")))?
            }
            PatternSubjectRef::ListHead(list) => {
                let source = self.subject_id(list)?;
                self.builder
                    .add_projected_subject(source, ProjectionKind::ListHead)
                    .map_err(|err| SourcePatternError::DispatchMatrix(format!("{err:?}")))?
            }
            PatternSubjectRef::ListTail(list) => {
                let source = self.subject_id(list)?;
                self.builder
                    .add_projected_subject(source, ProjectionKind::ListTail)
                    .map_err(|err| SourcePatternError::DispatchMatrix(format!("{err:?}")))?
            }
            PatternSubjectRef::MapValue { map, key } => {
                let source = self.subject_id(map)?;
                self.builder
                    .add_projected_subject(source, ProjectionKind::MapValue { key: key.clone() })
                    .map_err(|err| SourcePatternError::DispatchMatrix(format!("{err:?}")))?
            }
            PatternSubjectRef::BitstringField { bitstring, index } => {
                let source = self.subject_id(bitstring)?;
                self.builder
                    .add_projected_subject(source, ProjectionKind::BitstringField(*index))
                    .map_err(|err| SourcePatternError::DispatchMatrix(format!("{err:?}")))?
            }
        };
        self.subjects.insert(subject.clone(), id);
        Ok(id)
    }

    fn map_key(&mut self, pattern: &Pattern) -> Result<DispatchConst, SourcePatternError> {
        match pattern {
            Pattern::Int(value) => Ok(DispatchConst::Int(*value)),
            Pattern::Float(value) => Ok(DispatchConst::FloatBits(value.to_bits())),
            Pattern::Binary(bytes) => Ok(DispatchConst::Utf8Binary(bytes.clone())),
            Pattern::Atom(name) => Ok(DispatchConst::AtomName(name.clone())),
            Pattern::Bool(value) => Ok(DispatchConst::Bool(*value)),
            Pattern::Nil => Ok(DispatchConst::Nil),
            _ => Err(SourcePatternError::UnsupportedMapKey),
        }
    }

    fn prepare_heap_key(&mut self, key: &DispatchConst) {
        if !matches!(
            key,
            DispatchConst::FloatBits(_) | DispatchConst::AtomName(_) | DispatchConst::Utf8Binary(_)
        ) {
            return;
        }
        if !self.prepared_keys.contains(key) {
            self.prepared_keys.push(key.clone());
        }
    }

    fn subject_refs_by_id(&self) -> Vec<Option<PatternSubjectRef>> {
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

fn validate_source_order(patterns: &SourcePatternRows) -> Result<(), SourcePatternError> {
    for pair in patterns.rows.windows(2) {
        let previous = pair[0].body_id;
        let current = pair[1].body_id;
        if previous >= current {
            return Err(SourcePatternError::NonMonotonicBodyId { previous, current });
        }
    }
    Ok(())
}

fn bitstring_field_kind(kind: BitType) -> BitstringFieldKind {
    match kind {
        BitType::Integer => BitstringFieldKind::Integer,
        BitType::Float => BitstringFieldKind::Float,
        BitType::Binary => BitstringFieldKind::Binary,
        BitType::Bits => BitstringFieldKind::Bits,
        BitType::Utf8 => BitstringFieldKind::Utf8,
        BitType::Utf16 => BitstringFieldKind::Utf16,
        BitType::Utf32 => BitstringFieldKind::Utf32,
    }
}

fn bitstring_endian(endian: Endian) -> BitstringEndian {
    match endian {
        Endian::Big => BitstringEndian::Big,
        Endian::Little => BitstringEndian::Little,
        Endian::Native => BitstringEndian::Native,
    }
}

fn remap_span(span: &mut Span, remap: &HashMap<FileId, FileId>) {
    if let Some(&to) = remap.get(&span.file) {
        span.file = to;
    }
}
