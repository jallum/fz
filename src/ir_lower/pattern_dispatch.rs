use super::*;
use crate::ast::{BitType, Endian, Expr, Pattern, Spanned};
use crate::compiler::source::Span;
use crate::dispatch_matrix::pattern::{
    PatternBodyId, PatternRow, SourcePatternError, SourcePatternRows, collect_guard_capture_names,
};
use crate::dispatch_matrix::pattern::{
    PatternDispatchPlan, PatternGuardBinOp, PatternGuardDispatch, PatternGuardExpr, PatternGuardUnaryOp,
    PatternSubjectRef, guard_expr_from_ast, pattern_dispatch_from_source_with_guard_resolver,
};
use crate::dispatch_matrix::{
    BitstringEndian, BitstringFieldKind, BitstringFieldSize, BitstringShape, ComparisonValue, DispatchConst,
    DispatchNode, EdgeEvidence, GraphNodeId, PinnedValueId, ProjectionKind, Region, SubjectId,
};
use crate::fz_ir::{BinOp, BitSizeIr, BlockId, Const, Prim, Term, UnOp, Var};
use crate::types::{Ty, Types};
use std::collections::hash_map::Entry;
use std::collections::{BTreeSet, HashMap};

pub(super) type BodyCb<'a, T> = &'a mut dyn FnMut(
    &mut LowerCtx,
    &mut T,
    PatternBodyId,
    Vec<MatchedBinding>,
    Vec<(Var, Ty)>,
    Option<Spanned<Expr>>,
    BlockId,
) -> Result<(), LowerError>;

#[derive(Debug, Clone)]
pub(crate) struct MatchedBinding {
    pub name: String,
    pub var: Var,
    pub source: PatternSubjectRef,
}

#[derive(Debug, Clone, Default)]
pub(super) struct PatternLowerState {
    inputs: Vec<Var>,
    values: HashMap<SubjectId, Var>,
    bitstring_fields: HashMap<(SubjectId, u32), Var>,
    direct_bindings: HashMap<String, Var>,
}

pub(crate) fn lower_source_patterns_to_current_fn<T: Types<Ty = Ty>>(
    ctx: &mut LowerCtx,
    t: &mut T,
    source_patterns: SourcePatternRows,
    fail_block: BlockId,
    body_cb: BodyCb<'_, T>,
) -> Result<(), LowerError> {
    let mut guard_stack = Vec::new();
    let mut guard_resolver = |name: &str, arity: usize, args: Vec<PatternGuardExpr>| {
        lower_guard_helper_call_to_dispatch(ctx, name, arity, args, &mut guard_stack)
    };
    let plan =
        pattern_dispatch_from_source_with_guard_resolver(source_patterns, &mut guard_resolver).map_err(|err| {
            LowerError::Unsupported {
                span: Span::DUMMY,
                what: format!("source pattern dispatch cannot be represented: {:?}", err),
            }
        })?;
    let mut state = PatternLowerState::default();
    lower_dispatch_node(ctx, t, &plan, plan.graph.root, fail_block, body_cb, &mut state)
}

pub(super) fn lower_dispatch_node<T: Types<Ty = Ty>>(
    ctx: &mut LowerCtx,
    t: &mut T,
    plan: &PatternDispatchPlan,
    node_id: GraphNodeId,
    fail_block: BlockId,
    body_cb: BodyCb<'_, T>,
    state: &mut PatternLowerState,
) -> Result<(), LowerError> {
    let Some(node) = plan.graph.node(node_id).cloned() else {
        return Err(LowerError::Unsupported {
            span: Span::DUMMY,
            what: format!("dispatch graph node {:?} is out of bounds", node_id),
        });
    };
    match node {
        DispatchNode::Fail => {
            if !ctx.terminated {
                ctx.set_term(Term::Goto(fail_block, vec![]));
            }
            Ok(())
        }
        DispatchNode::Outcome { outcome, .. } => {
            let outcome = plan.outcome(outcome).ok_or_else(|| LowerError::Unsupported {
                span: Span::DUMMY,
                what: format!("dispatch outcome {:?} is out of bounds", outcome),
            })?;
            let bindings = outcome
                .bindings
                .iter()
                .map(|binding| {
                    let source = plan
                        .subject_ref(binding.source)
                        .cloned()
                        .ok_or_else(|| LowerError::Unsupported {
                            span: binding.span,
                            what: format!("binding source {:?} is missing", binding.source),
                        })?;
                    Ok(MatchedBinding {
                        name: binding.name.clone(),
                        var: materialize_dispatch_subject(ctx, plan, binding.source, state)?,
                        source,
                    })
                })
                .collect::<Result<Vec<_>, LowerError>>()?;
            body_cb(ctx, t, outcome.body_id, bindings, Vec::new(), None, fail_block)
        }
        DispatchNode::Test {
            predicate,
            on_match,
            on_miss,
        } => lower_dispatch_test(
            ctx,
            t,
            plan,
            predicate.subject,
            predicate.region,
            on_match,
            on_miss,
            fail_block,
            body_cb,
            state,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn lower_dispatch_test<T: Types<Ty = Ty>>(
    ctx: &mut LowerCtx,
    t: &mut T,
    plan: &PatternDispatchPlan,
    subject: SubjectId,
    region: Region,
    on_match: crate::dispatch_matrix::DispatchEdge,
    on_miss: crate::dispatch_matrix::DispatchEdge,
    fail_block: BlockId,
    body_cb: BodyCb<'_, T>,
    state: &mut PatternLowerState,
) -> Result<(), LowerError> {
    let true_b = ctx.cur_mut().block(vec![]);
    let false_b = ctx.cur_mut().block(vec![]);
    let mut true_state = state.clone();
    if let Region::Bitstring(shape) = &region {
        lower_bitstring_test(ctx, plan, subject, shape, true_b, false_b, &mut true_state)?;
    } else {
        let (test, proven_values) = lower_region_predicate(ctx, t, plan, subject, &region, &on_match.evidence, state)?;
        true_state.values.extend(proven_values);
        ctx.set_if_term(test, true_b, false_b);
    }
    ctx.cur_block = Some(true_b);
    ctx.terminated = false;
    apply_edge_evidence(ctx, plan, &on_match.evidence, &mut true_state)?;
    lower_dispatch_node(ctx, t, plan, on_match.target, fail_block, body_cb, &mut true_state)?;
    ctx.cur_block = Some(false_b);
    ctx.terminated = false;
    lower_dispatch_node(ctx, t, plan, on_miss.target, fail_block, body_cb, state)
}

fn apply_edge_evidence(
    ctx: &mut LowerCtx,
    plan: &PatternDispatchPlan,
    evidence: &EdgeEvidence,
    state: &mut PatternLowerState,
) -> Result<(), LowerError> {
    for projection in &evidence.projections {
        if state.values.contains_key(&projection.result) {
            continue;
        }
        if let ProjectionKind::BitstringField(index) = projection.kind
            && let Some(value) = state.bitstring_fields.get(&(projection.source, index)).copied()
        {
            state.values.insert(projection.result, value);
            continue;
        }
        materialize_dispatch_subject(ctx, plan, projection.result, state)?;
    }
    Ok(())
}

fn lower_region_predicate<T: Types<Ty = Ty>>(
    ctx: &mut LowerCtx,
    t: &mut T,
    plan: &PatternDispatchPlan,
    subject: SubjectId,
    region: &Region,
    evidence: &EdgeEvidence,
    state: &mut PatternLowerState,
) -> Result<(Var, Vec<(SubjectId, Var)>), LowerError> {
    let mut true_values = Vec::new();
    let test = match region {
        Region::Any => ctx.let_(Prim::Const(Const::True)),
        Region::Never => ctx.let_(Prim::Const(Const::False)),
        Region::Type(ty) => {
            let subject = materialize_dispatch_subject(ctx, plan, subject, state)?;
            ctx.let_(Prim::TypeTest(subject, Box::new(ty.clone())))
        }
        Region::Equal(ComparisonValue::Const(value)) => {
            let subject = materialize_dispatch_subject(ctx, plan, subject, state)?;
            match value {
                DispatchConst::EmptyList => ctx.let_(Prim::IsEmptyList(subject)),
                _ => {
                    let lit = lower_dispatch_const(ctx, value)?;
                    ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit))
                }
            }
        }
        Region::Equal(ComparisonValue::Pinned(pinned)) => {
            let subject = materialize_dispatch_subject(ctx, plan, subject, state)?;
            let pinned = lower_pinned_var(ctx, plan, *pinned, state)?;
            ctx.let_(Prim::BinOp(BinOp::Eq, subject, pinned))
        }
        Region::TupleArity(arity) => {
            let subject = materialize_dispatch_subject(ctx, plan, subject, state)?;
            let tuple_ty = concrete_any_tuple(t, *arity as usize);
            ctx.let_(Prim::TypeTest(subject, Box::new(tuple_ty)))
        }
        Region::List(crate::dispatch_matrix::ListRegion::Empty) => {
            let subject = materialize_dispatch_subject(ctx, plan, subject, state)?;
            ctx.let_(Prim::IsEmptyList(subject))
        }
        Region::List(crate::dispatch_matrix::ListRegion::Cons) => {
            let subject = materialize_dispatch_subject(ctx, plan, subject, state)?;
            ctx.let_(Prim::IsListCons(subject))
        }
        Region::MapKind => {
            let subject = materialize_dispatch_subject(ctx, plan, subject, state)?;
            ctx.let_(Prim::TypeTest(subject, Box::new(concrete_any_map(t))))
        }
        Region::MapKeyPresent { key } => {
            let map = materialize_dispatch_subject(ctx, plan, subject, state)?;
            let key_var = lower_dispatch_const(ctx, key)?;
            let value = ctx.let_(Prim::MatcherMapGet(map, key_var));
            if let Some(result) = projection_result(
                evidence,
                subject,
                |kind| matches!(kind, ProjectionKind::MapValue { key: projection_key } if projection_key == key),
            ) {
                true_values.push((result, value));
            }
            let miss = ctx.let_(Prim::IsMatcherMapMiss(value));
            let false_v = ctx.let_(Prim::Const(Const::False));
            ctx.let_(Prim::BinOp(BinOp::Eq, miss, false_v))
        }
        Region::Guard(guard) => {
            let expr = plan
                .guards
                .get(guard.0 as usize)
                .ok_or_else(|| LowerError::Unsupported {
                    span: Span::DUMMY,
                    what: format!("guard {:?} is out of bounds", guard),
                })?;
            lower_guard_expr(ctx, t, plan, expr, state)?
        }
        Region::Bitstring(_) => {
            return Err(LowerError::Unsupported {
                span: Span::DUMMY,
                what: "bitstring dispatch must use lower_bitstring_test".into(),
            });
        }
    };
    Ok((test, true_values))
}

fn projection_result(
    evidence: &EdgeEvidence,
    source: SubjectId,
    pred: impl Fn(&ProjectionKind) -> bool,
) -> Option<SubjectId> {
    evidence
        .projections
        .iter()
        .find(|projection| projection.source == source && pred(&projection.kind))
        .map(|projection| projection.result)
}

pub(super) fn materialize_dispatch_subject(
    ctx: &mut LowerCtx,
    plan: &PatternDispatchPlan,
    subject: SubjectId,
    state: &mut PatternLowerState,
) -> Result<Var, LowerError> {
    if let Some(var) = state.values.get(&subject).copied() {
        return Ok(var);
    }
    let Some(subject_data) = plan.matrix.subjects.get(subject.0 as usize) else {
        return Err(LowerError::Unsupported {
            span: Span::DUMMY,
            what: format!("dispatch subject {:?} is out of bounds", subject),
        });
    };
    let var = match &subject_data.source {
        crate::dispatch_matrix::SubjectSource::Input { ordinal } => state
            .inputs
            .get(*ordinal as usize)
            .copied()
            .or_else(|| plan.inputs.get(*ordinal as usize).and_then(|input| input.var))
            .ok_or_else(|| LowerError::Unsupported {
                span: Span::DUMMY,
                what: format!("dispatch input {} has no IR var", ordinal),
            })?,
        crate::dispatch_matrix::SubjectSource::Projection(projection) => match &projection.kind {
            ProjectionKind::TupleField(index) => {
                let tuple = materialize_dispatch_subject(ctx, plan, projection.source, state)?;
                ctx.let_(Prim::TupleField(tuple, *index))
            }
            ProjectionKind::ListHead => {
                let list = materialize_dispatch_subject(ctx, plan, projection.source, state)?;
                ctx.let_(Prim::ListHead(list))
            }
            ProjectionKind::ListTail => {
                let list = materialize_dispatch_subject(ctx, plan, projection.source, state)?;
                ctx.let_(Prim::ListTail(list))
            }
            ProjectionKind::MapValue { key } => {
                let map = materialize_dispatch_subject(ctx, plan, projection.source, state)?;
                let key = lower_dispatch_const(ctx, key)?;
                ctx.let_(Prim::MapGet(map, key))
            }
            ProjectionKind::BitstringField(index) => state
                .bitstring_fields
                .get(&(projection.source, *index))
                .copied()
                .ok_or_else(|| LowerError::Unsupported {
                    span: Span::DUMMY,
                    what: format!("bitstring field {:?}/{} not available", projection.source, index),
                })?,
        },
    };
    state.values.insert(subject, var);
    Ok(var)
}

pub(super) fn lower_dispatch_const(ctx: &mut LowerCtx, value: &DispatchConst) -> Result<Var, LowerError> {
    Ok(match value {
        DispatchConst::Int(n) => ctx.let_(Prim::Const(Const::Int(*n))),
        DispatchConst::FloatBits(bits) => ctx.let_(Prim::Const(Const::Float(f64::from_bits(*bits)))),
        DispatchConst::AtomName(name) => {
            let atom = ctx.atoms.intern(name);
            ctx.let_(Prim::Const(Const::Atom(atom)))
        }
        DispatchConst::Bool(true) => ctx.let_(Prim::Const(Const::True)),
        DispatchConst::Bool(false) => ctx.let_(Prim::Const(Const::False)),
        DispatchConst::Nil => ctx.let_(Prim::Const(Const::Nil)),
        DispatchConst::Utf8Binary(bytes) => {
            let bit_len = (bytes.len() * 8) as u64;
            let bs = ctx.let_(Prim::ConstBitstring(bytes.clone(), bit_len));
            ctx.let_(Prim::Brand(bs, "utf8".to_string()))
        }
        DispatchConst::EmptyList => {
            return Err(LowerError::Unsupported {
                span: Span::DUMMY,
                what: "empty-list constant cannot be materialized as an IR literal".into(),
            });
        }
    })
}

fn lower_pinned_var(
    ctx: &LowerCtx,
    plan: &PatternDispatchPlan,
    pinned: PinnedValueId,
    state: &PatternLowerState,
) -> Result<Var, LowerError> {
    let pinned = plan
        .pinned
        .get(pinned.0 as usize)
        .ok_or_else(|| LowerError::Unsupported {
            span: Span::DUMMY,
            what: format!("pinned slot {:?} out of bounds", pinned),
        })?;
    if let Some(input) = pinned.var {
        return state
            .inputs
            .get(input.0 as usize)
            .copied()
            .or(Some(input))
            .ok_or_else(|| LowerError::Unsupported {
                span: pinned.span,
                what: format!("pinned helper input {:?} out of bounds", input),
            });
    }
    ctx.lookup(&pinned.name).ok_or_else(|| LowerError::Unbound {
        span: pinned.span,
        name: format!("^{}", pinned.name),
    })
}

fn lower_bitstring_test(
    ctx: &mut LowerCtx,
    plan: &PatternDispatchPlan,
    subject: SubjectId,
    shape: &BitstringShape,
    success_block: BlockId,
    fail_block: BlockId,
    state: &mut PatternLowerState,
) -> Result<(), LowerError> {
    let subject_v = materialize_dispatch_subject(ctx, plan, subject, state)?;
    let mut reader = ctx.let_(Prim::BitReaderInit(subject_v));
    for (index, field) in shape.fields.iter().enumerate() {
        let size = lower_bit_size(ctx, &field.size, state)?;
        let result = ctx.let_(Prim::BitReadField {
            reader,
            ty: bit_type_to_ast(field.kind),
            size,
            endian: endian_to_ast(field.endian),
            signed: field.signed,
            unit: field.unit,
            is_last: index + 1 == shape.fields.len(),
        });
        let ok = ctx.let_(Prim::TupleField(result, 0));
        let cont_b = ctx.cur_mut().block(vec![]);
        ctx.set_if_term(ok, cont_b, fail_block);
        ctx.cur_block = Some(cont_b);
        ctx.terminated = false;
        let extracted = ctx.let_(Prim::TupleField(result, 1));
        reader = ctx.let_(Prim::TupleField(result, 2));
        state.bitstring_fields.insert((subject, index as u32), extracted);
        if let Some(names) = plan
            .bitstring_direct_bindings
            .get(&bitstring_field_subject(plan, subject, index as u32)?)
        {
            for name in names {
                state.direct_bindings.insert(name.clone(), extracted);
            }
        }
    }
    let done = ctx.let_(Prim::BitReaderDone(reader));
    ctx.set_if_term(done, success_block, fail_block);
    Ok(())
}

fn bitstring_field_subject(plan: &PatternDispatchPlan, source: SubjectId, index: u32) -> Result<SubjectId, LowerError> {
    plan.matrix
        .subjects
        .iter()
        .find_map(|subject| match &subject.source {
            crate::dispatch_matrix::SubjectSource::Projection(projection)
                if projection.source == source && projection.kind == ProjectionKind::BitstringField(index) =>
            {
                Some(subject.id)
            }
            _ => None,
        })
        .ok_or_else(|| LowerError::Unsupported {
            span: Span::DUMMY,
            what: format!("bitstring field subject {:?}/{} missing", source, index),
        })
}

fn lower_bit_size(
    ctx: &LowerCtx,
    size: &Option<BitstringFieldSize>,
    state: &PatternLowerState,
) -> Result<Option<BitSizeIr>, LowerError> {
    Ok(match size {
        None => None,
        Some(BitstringFieldSize::Literal(n)) => Some(BitSizeIr::Literal(*n)),
        Some(BitstringFieldSize::Binding(subject)) => {
            let v = state
                .values
                .get(subject)
                .copied()
                .ok_or_else(|| LowerError::Unsupported {
                    span: Span::DUMMY,
                    what: format!("bitstring size subject {:?} not available", subject),
                })?;
            Some(BitSizeIr::Var(v))
        }
        Some(BitstringFieldSize::BindingName(name)) => {
            let v = state
                .direct_bindings
                .get(name)
                .copied()
                .or_else(|| ctx.lookup(name))
                .ok_or_else(|| LowerError::Unbound {
                    span: Span::DUMMY,
                    name: format!("bit size var {}", name),
                })?;
            Some(BitSizeIr::Var(v))
        }
    })
}

fn lower_guard_expr<T: Types<Ty = Ty>>(
    ctx: &mut LowerCtx,
    t: &mut T,
    plan: &PatternDispatchPlan,
    expr: &PatternGuardExpr,
    state: &mut PatternLowerState,
) -> Result<Var, LowerError> {
    Ok(match expr {
        PatternGuardExpr::Const(value) => lower_dispatch_const(ctx, value)?,
        PatternGuardExpr::Subject(subject) => materialize_dispatch_subject(ctx, plan, *subject, state)?,
        PatternGuardExpr::Pinned(pinned) => lower_pinned_var(ctx, plan, *pinned, state)?,
        PatternGuardExpr::Unary { op, expr } => {
            let value = lower_guard_expr(ctx, t, plan, expr, state)?;
            match op {
                PatternGuardUnaryOp::Not => ctx.let_(Prim::UnOp(UnOp::Not, value)),
                PatternGuardUnaryOp::Neg => ctx.let_(Prim::UnOp(UnOp::Neg, value)),
            }
        }
        PatternGuardExpr::Binary { op, lhs, rhs } => {
            let lhs = lower_guard_expr(ctx, t, plan, lhs, state)?;
            let rhs = lower_guard_expr(ctx, t, plan, rhs, state)?;
            let op = match op {
                PatternGuardBinOp::Add => BinOp::Add,
                PatternGuardBinOp::Sub => BinOp::Sub,
                PatternGuardBinOp::Mul => BinOp::Mul,
                PatternGuardBinOp::Div => BinOp::Div,
                PatternGuardBinOp::Rem => BinOp::Mod,
                PatternGuardBinOp::Eq => BinOp::Eq,
                PatternGuardBinOp::Neq => BinOp::Neq,
                PatternGuardBinOp::Lt => BinOp::Lt,
                PatternGuardBinOp::LtEq => BinOp::Le,
                PatternGuardBinOp::Gt => BinOp::Gt,
                PatternGuardBinOp::GtEq => BinOp::Ge,
                PatternGuardBinOp::And => BinOp::And,
                PatternGuardBinOp::Or => BinOp::Or,
            };
            ctx.let_(Prim::BinOp(op, lhs, rhs))
        }
        PatternGuardExpr::Dispatch { inputs, dispatch } => lower_guard_dispatch(ctx, t, plan, inputs, dispatch, state)?,
    })
}

fn lower_guard_dispatch<T: Types<Ty = Ty>>(
    ctx: &mut LowerCtx,
    t: &mut T,
    parent_plan: &PatternDispatchPlan,
    inputs: &[PatternGuardExpr],
    dispatch: &PatternGuardDispatch,
    state: &mut PatternLowerState,
) -> Result<Var, LowerError> {
    let input_vars = inputs
        .iter()
        .map(|input| lower_guard_expr(ctx, t, parent_plan, input, state))
        .collect::<Result<Vec<_>, _>>()?;
    let done_value = ctx.cur_mut().fresh_var();
    let done_b = ctx.cur_mut().block(vec![done_value]);
    let fail_b = ctx.cur_mut().block(vec![]);
    let mut dispatch_state = PatternLowerState {
        inputs: input_vars,
        ..PatternLowerState::default()
    };
    lower_guard_dispatch_node(
        ctx,
        t,
        &dispatch.plan,
        &dispatch.bodies,
        dispatch.plan.graph.root,
        done_b,
        fail_b,
        &mut dispatch_state,
    )?;
    ctx.cur_block = Some(fail_b);
    ctx.terminated = false;
    let false_value = ctx.let_(Prim::Const(Const::False));
    ctx.set_term(Term::Goto(done_b, vec![false_value]));
    ctx.cur_block = Some(done_b);
    ctx.terminated = false;
    Ok(done_value)
}

#[allow(clippy::too_many_arguments)]
fn lower_guard_dispatch_node<T: Types<Ty = Ty>>(
    ctx: &mut LowerCtx,
    t: &mut T,
    plan: &PatternDispatchPlan,
    bodies: &[PatternGuardExpr],
    node_id: GraphNodeId,
    done_b: BlockId,
    fail_b: BlockId,
    state: &mut PatternLowerState,
) -> Result<(), LowerError> {
    let Some(node) = plan.graph.node(node_id).cloned() else {
        return Err(LowerError::Unsupported {
            span: Span::DUMMY,
            what: format!("guard dispatch graph node {:?} is out of bounds", node_id),
        });
    };
    match node {
        DispatchNode::Fail => {
            ctx.set_term(Term::Goto(fail_b, vec![]));
            Ok(())
        }
        DispatchNode::Outcome { outcome, .. } => {
            let outcome = plan.outcome(outcome).ok_or_else(|| LowerError::Unsupported {
                span: Span::DUMMY,
                what: format!("guard dispatch outcome {:?} is out of bounds", outcome),
            })?;
            let body = bodies
                .get(outcome.body_id as usize)
                .ok_or_else(|| LowerError::Unsupported {
                    span: outcome.span,
                    what: format!("guard dispatch body {} is out of bounds", outcome.body_id),
                })?;
            let value = lower_guard_expr(ctx, t, plan, body, state)?;
            ctx.set_term(Term::Goto(done_b, vec![value]));
            Ok(())
        }
        DispatchNode::Test {
            predicate,
            on_match,
            on_miss,
        } => {
            let true_b = ctx.cur_mut().block(vec![]);
            let false_b = ctx.cur_mut().block(vec![]);
            let mut true_state = state.clone();
            if let Region::Bitstring(shape) = &predicate.region {
                lower_bitstring_test(ctx, plan, predicate.subject, shape, true_b, false_b, &mut true_state)?;
            } else {
                let (test, proven_values) = lower_region_predicate(
                    ctx,
                    t,
                    plan,
                    predicate.subject,
                    &predicate.region,
                    &on_match.evidence,
                    state,
                )?;
                true_state.values.extend(proven_values);
                ctx.set_if_term(test, true_b, false_b);
            }
            ctx.cur_block = Some(true_b);
            ctx.terminated = false;
            apply_edge_evidence(ctx, plan, &on_match.evidence, &mut true_state)?;
            lower_guard_dispatch_node(ctx, t, plan, bodies, on_match.target, done_b, fail_b, &mut true_state)?;
            ctx.cur_block = Some(false_b);
            ctx.terminated = false;
            lower_guard_dispatch_node(ctx, t, plan, bodies, on_miss.target, done_b, fail_b, state)
        }
    }
}

pub(crate) fn lower_guard_helper_call_to_dispatch(
    ctx: &LowerCtx,
    name: &str,
    arity: usize,
    args: Vec<PatternGuardExpr>,
    stack: &mut Vec<(String, usize)>,
) -> Result<Option<PatternGuardExpr>, SourcePatternError> {
    let key = (name.to_string(), arity);
    let Some(fn_def) = ctx.fn_defs_by_arity.get(&key) else {
        return Ok(None);
    };
    if stack.contains(&key) {
        return Err(SourcePatternError::GuardCallCycle(key.0, key.1));
    }
    if fn_def.clauses.is_empty() || fn_def.clauses.iter().any(|clause| clause.params.len() != arity) {
        return Ok(None);
    }

    stack.push(key);
    let subjects: Vec<Var> = (0..arity).map(|i| Var(i as u32)).collect();
    let source_patterns = SourcePatternRows {
        subjects,
        rows: fn_def
            .clauses
            .iter()
            .enumerate()
            .map(|(i, clause)| PatternRow {
                patterns: clause.params.clone(),
                preconditions: Vec::new(),
                guard: clause.guard.clone(),
                body_id: i as PatternBodyId,
            })
            .collect(),
    };
    let mut resolver = |callee: &str, callee_arity: usize, callee_args: Vec<PatternGuardExpr>| {
        lower_guard_helper_call_to_dispatch(ctx, callee, callee_arity, callee_args, stack)
    };
    let plan_result = pattern_dispatch_from_source_with_guard_resolver(source_patterns, &mut resolver);
    stack.pop();
    let mut plan = plan_result.map_err(|err| SourcePatternError::DispatchMatrix(format!("{err:?}")))?;

    let param_input_by_name: HashMap<String, Var> = fn_def.clauses[0]
        .params
        .iter()
        .enumerate()
        .filter_map(|(i, pattern)| match &pattern.node {
            Pattern::Var(name) => Some((name.clone(), Var(i as u32))),
            _ => None,
        })
        .collect();
    for pinned in &mut plan.pinned {
        if let Some(input) = param_input_by_name.get(&pinned.name) {
            pinned.var = Some(*input);
        }
    }

    let mut pinned_by_name: HashMap<String, PinnedValueId> = plan
        .pinned
        .iter()
        .enumerate()
        .map(|(i, pinned)| (pinned.name.clone(), PinnedValueId(i as u32)))
        .collect();
    for clause in &fn_def.clauses {
        let mut bound = BTreeSet::new();
        for pattern in &clause.params {
            let mut names = Vec::new();
            collect_pattern_bound_names(&pattern.node, &mut names);
            bound.extend(names);
        }
        let mut captures = Vec::new();
        collect_guard_capture_names(&clause.body.node, &bound, &mut captures);
        for capture in captures {
            if let Entry::Vacant(entry) = pinned_by_name.entry(capture) {
                let id = PinnedValueId(plan.pinned.len() as u32);
                plan.pinned.push(crate::dispatch_matrix::pattern::PatternPinnedInput {
                    name: entry.key().clone(),
                    var: None,
                    span: clause.body.span,
                });
                entry.insert(id);
            }
        }
    }

    let mut bodies = Vec::with_capacity(fn_def.clauses.len());
    for clause in &fn_def.clauses {
        let outcome = plan
            .outcomes
            .iter()
            .find(|outcome| outcome.body_id as usize == bodies.len())
            .ok_or(SourcePatternError::UnsupportedGuardExpr)?;
        let bindings = outcome
            .bindings
            .iter()
            .map(|binding| (binding.name.clone(), binding.source))
            .collect::<HashMap<_, _>>();
        let mut resolver = |callee: &str, callee_arity: usize, callee_args: Vec<PatternGuardExpr>| {
            lower_guard_helper_call_to_dispatch(ctx, callee, callee_arity, callee_args, stack)
        };
        bodies.push(guard_expr_from_ast(
            &clause.body.node,
            &bindings,
            &pinned_by_name,
            &mut resolver,
        )?);
    }

    Ok(Some(PatternGuardExpr::Dispatch {
        inputs: args,
        dispatch: Box::new(PatternGuardDispatch {
            plan: Box::new(plan),
            bodies,
        }),
    }))
}

pub(crate) fn collect_dispatch_pinned_names_recursive(plan: &PatternDispatchPlan, out: &mut Vec<String>) {
    for pinned in &plan.pinned {
        if pinned.var.is_some() {
            continue;
        }
        if !out.contains(&pinned.name) {
            out.push(pinned.name.clone());
        }
    }
    for guard in &plan.guards {
        collect_guard_expr_dispatch_pinned(guard, out);
    }
}

pub(crate) fn collect_guard_expr_dispatch_pinned(expr: &PatternGuardExpr, out: &mut Vec<String>) {
    match expr {
        PatternGuardExpr::Unary { expr, .. } => collect_guard_expr_dispatch_pinned(expr, out),
        PatternGuardExpr::Binary { lhs, rhs, .. } => {
            collect_guard_expr_dispatch_pinned(lhs, out);
            collect_guard_expr_dispatch_pinned(rhs, out);
        }
        PatternGuardExpr::Dispatch { inputs, dispatch } => {
            for input in inputs {
                collect_guard_expr_dispatch_pinned(input, out);
            }
            collect_dispatch_pinned_names_recursive(&dispatch.plan, out);
            for body in &dispatch.bodies {
                collect_guard_expr_dispatch_pinned(body, out);
            }
        }
        PatternGuardExpr::Const(_) | PatternGuardExpr::Subject(_) | PatternGuardExpr::Pinned(_) => {}
    }
}

pub(crate) fn materialize_prepared_dispatch_key(ctx: &mut LowerCtx, key: &DispatchConst) -> Result<Var, LowerError> {
    lower_dispatch_const(ctx, key)
}

fn bit_type_to_ast(kind: BitstringFieldKind) -> BitType {
    match kind {
        BitstringFieldKind::Integer => BitType::Integer,
        BitstringFieldKind::Float => BitType::Float,
        BitstringFieldKind::Binary => BitType::Binary,
        BitstringFieldKind::Bits => BitType::Bits,
        BitstringFieldKind::Utf8 => BitType::Utf8,
        BitstringFieldKind::Utf16 => BitType::Utf16,
        BitstringFieldKind::Utf32 => BitType::Utf32,
    }
}

fn endian_to_ast(endian: BitstringEndian) -> Endian {
    match endian {
        BitstringEndian::Big => Endian::Big,
        BitstringEndian::Little => Endian::Little,
        BitstringEndian::Native => Endian::Native,
    }
}
