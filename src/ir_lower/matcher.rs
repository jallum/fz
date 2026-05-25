use super::*;
use crate::ast::{
    BinOp as AstBinOp, BitField as AstBitField, BitSize as AstBitSize, Expr, FnClause, FnDef, Item,
    MatchClause, Pattern, Program, Spanned, UnOp as AstUnOp, WithBinding,
};
use crate::diag::Span;
use crate::fz_ir::{
    BinOp, BitFieldIr, BitSizeIr, BlockId, Const, Cont, ExternDecl, ExternId, ExternTy, FnBuilder,
    FnId, Module, ModuleBuilder, Prim, SourceInfo, Term, UnOp, Var,
};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

// fz-ul4.43.D.1 — PatternMatrix lowering (re-applied for diagnostic).
use crate::pattern_matrix::{BodyId, PatternMatrix, Row};

pub(super) type BodyCb<'a> = &'a mut dyn FnMut(
    &mut LowerCtx,
    BodyId,
    Vec<(String, Var)>,
    Vec<(Var, crate::types::Ty)>,
    Option<crate::ast::Spanned<crate::ast::Expr>>,
    BlockId,
) -> Result<(), LowerError>;

#[derive(Default)]
pub(super) struct MatcherLowerState {
    values: std::collections::HashMap<crate::matcher::SubjectRef, Var>,
    bitstring_fields: std::collections::HashMap<(crate::matcher::SubjectRef, u32), Var>,
    direct_bindings: std::collections::HashMap<String, Var>,
}

pub(super) fn lower_pattern_matrix_to_current_fn(
    ctx: &mut LowerCtx,
    pattern_matrix: PatternMatrix,
    fail_block: BlockId,
    body_cb: BodyCb<'_>,
) -> Result<(), LowerError> {
    let mut guard_stack = Vec::new();
    let mut guard_resolver = |name: &str, arity: usize, args: Vec<crate::matcher::GuardExpr>| {
        lower_guard_helper_call_to_dispatch(ctx, name, arity, args, &mut guard_stack)
    };
    let matcher = crate::pattern_matrix::compile_pattern_matrix_with_guard_resolver(
        pattern_matrix,
        &mut guard_resolver,
    )
    .map_err(|err| LowerError::Unsupported {
        span: Span::DUMMY,
        what: format!("matcher cannot be lowered inline: {:?}", err),
    })?;
    let mut state = MatcherLowerState::default();
    lower_matcher_node(ctx, &matcher, matcher.root, fail_block, body_cb, &mut state)
}

pub(super) fn lower_matcher_node(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    node_id: crate::matcher::NodeId,
    fail_block: BlockId,
    body_cb: BodyCb<'_>,
    state: &mut MatcherLowerState,
) -> Result<(), LowerError> {
    let Some(node) = matcher.node(node_id).cloned() else {
        return Err(LowerError::Unsupported {
            span: Span::DUMMY,
            what: format!("matcher node {:?} is out of bounds", node_id),
        });
    };
    match node {
        crate::matcher::MatcherNode::Fail { .. } => {
            if !ctx.terminated {
                ctx.set_term(Term::Goto(fail_block, vec![]));
            }
            Ok(())
        }
        crate::matcher::MatcherNode::Leaf(leaf) => {
            let bindings = leaf
                .bindings
                .into_iter()
                .map(|binding| {
                    Ok((
                        binding.name,
                        materialize_matcher_subject(ctx, matcher, &binding.source, state)?,
                    ))
                })
                .collect::<Result<Vec<_>, LowerError>>()?;
            body_cb(ctx, leaf.body_id, bindings, Vec::new(), None, fail_block)?;
            Ok(())
        }
        crate::matcher::MatcherNode::Switch {
            subject,
            kind,
            cases,
            default,
            ..
        } => lower_matcher_switch(
            ctx, matcher, subject, kind, cases, default, fail_block, body_cb, state,
        ),
        crate::matcher::MatcherNode::Test {
            test,
            on_true,
            on_false,
            ..
        } => lower_matcher_test(
            ctx, matcher, test, on_true, on_false, fail_block, body_cb, state,
        ),
        crate::matcher::MatcherNode::Guard {
            expr,
            on_true,
            on_false,
            ..
        } => {
            let guard = lower_matcher_guard_expr(ctx, matcher, &expr, state)?;
            let false_b = ctx.cur_mut().block(vec![]);
            let true_b = ctx.cur_mut().block(vec![]);
            ctx.set_if_term(guard, true_b, false_b);
            ctx.cur_block = Some(true_b);
            ctx.terminated = false;
            let mut true_state = clone_matcher_lower_state(state);
            lower_matcher_node(ctx, matcher, on_true, fail_block, body_cb, &mut true_state)?;
            ctx.cur_block = Some(false_b);
            ctx.terminated = false;
            lower_matcher_node(ctx, matcher, on_false, fail_block, body_cb, state)
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_matcher_switch(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    subject: crate::matcher::SubjectRef,
    kind: crate::matcher::SwitchKind,
    cases: Vec<(crate::matcher::SwitchKey, crate::matcher::NodeId)>,
    default: crate::matcher::NodeId,
    fail_block: BlockId,
    body_cb: BodyCb<'_>,
    state: &mut MatcherLowerState,
) -> Result<(), LowerError> {
    let subject_v = materialize_matcher_subject(ctx, matcher, &subject, state)?;
    for (key, case) in cases {
        let Some((test, branch_on_true)) =
            lower_matcher_switch_test(ctx, subject_v, kind.clone(), key)?
        else {
            continue;
        };
        let (match_b, next_b) = if branch_on_true {
            let next_b = ctx.cur_mut().block(vec![]);
            let match_b = ctx.cur_mut().block(vec![]);
            (match_b, next_b)
        } else {
            let match_b = ctx.cur_mut().block(vec![]);
            let next_b = ctx.cur_mut().block(vec![]);
            (match_b, next_b)
        };
        if branch_on_true {
            ctx.set_if_term(test, match_b, next_b);
        } else {
            ctx.set_if_term(test, next_b, match_b);
        }
        ctx.cur_block = Some(match_b);
        ctx.terminated = false;
        let mut case_state = clone_matcher_lower_state(state);
        lower_matcher_node(ctx, matcher, case, fail_block, body_cb, &mut case_state)?;
        ctx.cur_block = Some(next_b);
        ctx.terminated = false;
    }
    lower_matcher_node(ctx, matcher, default, fail_block, body_cb, state)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_matcher_test(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    test: crate::matcher::MatcherTest,
    on_true: crate::matcher::NodeId,
    on_false: crate::matcher::NodeId,
    fail_block: BlockId,
    body_cb: BodyCb<'_>,
    state: &mut MatcherLowerState,
) -> Result<(), LowerError> {
    if let crate::matcher::MatcherTest::Bitstring { subject, fields } = test {
        let true_b = ctx.cur_mut().block(vec![]);
        let false_b = ctx.cur_mut().block(vec![]);
        let mut true_state = clone_matcher_lower_state(state);
        lower_matcher_bitstring_test(
            ctx,
            matcher,
            &subject,
            &fields,
            true_b,
            false_b,
            &mut true_state,
        )?;
        ctx.cur_block = Some(true_b);
        ctx.terminated = false;
        lower_matcher_node(ctx, matcher, on_true, fail_block, body_cb, &mut true_state)?;
        ctx.cur_block = Some(false_b);
        ctx.terminated = false;
        return lower_matcher_node(ctx, matcher, on_false, fail_block, body_cb, state);
    }

    let (test_var, true_values) = lower_matcher_bool_test(ctx, matcher, &test, state)?;
    let false_b = ctx.cur_mut().block(vec![]);
    let true_b = ctx.cur_mut().block(vec![]);
    ctx.set_if_term(test_var, true_b, false_b);
    ctx.cur_block = Some(true_b);
    ctx.terminated = false;
    let mut true_state = clone_matcher_lower_state(state);
    true_state.values.extend(true_values);
    lower_matcher_node(ctx, matcher, on_true, fail_block, body_cb, &mut true_state)?;
    ctx.cur_block = Some(false_b);
    ctx.terminated = false;
    lower_matcher_node(ctx, matcher, on_false, fail_block, body_cb, state)
}

pub(super) fn clone_matcher_lower_state(state: &MatcherLowerState) -> MatcherLowerState {
    MatcherLowerState {
        values: state.values.clone(),
        bitstring_fields: state.bitstring_fields.clone(),
        direct_bindings: state.direct_bindings.clone(),
    }
}

pub(super) fn materialize_matcher_subject(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    subject: &crate::matcher::SubjectRef,
    state: &mut MatcherLowerState,
) -> Result<Var, LowerError> {
    if let Some(var) = state.values.get(subject).copied() {
        return Ok(var);
    }

    let var = match subject {
        crate::matcher::SubjectRef::Input(id) => matcher
            .inputs
            .get(id.0 as usize)
            .and_then(|input| input.var)
            .ok_or_else(|| LowerError::Unsupported {
                span: Span::DUMMY,
                what: format!("inline matcher input {:?} has no IR var", id),
            })?,
        crate::matcher::SubjectRef::TupleField { tuple, index } => {
            let tuple = materialize_matcher_subject(ctx, matcher, tuple, state)?;
            ctx.let_(Prim::TupleField(tuple, *index))
        }
        crate::matcher::SubjectRef::ListHead(list) => {
            let list = materialize_matcher_subject(ctx, matcher, list, state)?;
            ctx.let_(Prim::ListHead(list))
        }
        crate::matcher::SubjectRef::ListTail(list) => {
            let list = materialize_matcher_subject(ctx, matcher, list, state)?;
            ctx.let_(Prim::ListTail(list))
        }
        crate::matcher::SubjectRef::MapValue { map, key } => {
            let map = materialize_matcher_subject(ctx, matcher, map, state)?;
            let key = lower_matcher_const(ctx, matcher, key)?;
            ctx.let_(Prim::MapGet(map, key))
        }
        crate::matcher::SubjectRef::BitstringField { bitstring, index } => state
            .bitstring_fields
            .get(&((**bitstring).clone(), *index))
            .copied()
            .ok_or_else(|| LowerError::Unsupported {
                span: Span::DUMMY,
                what: format!("bitstring field {:?}/{} not available", bitstring, index),
            })?,
    };
    state.values.insert(subject.clone(), var);
    Ok(var)
}

pub(super) fn lower_matcher_const(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    value: &crate::matcher::MatcherConst,
) -> Result<Var, LowerError> {
    Ok(match value {
        crate::matcher::MatcherConst::Int(n) => ctx.let_(Prim::Const(Const::Int(*n))),
        crate::matcher::MatcherConst::FloatBits(bits) => {
            ctx.let_(Prim::Const(Const::Float(f64::from_bits(*bits))))
        }
        crate::matcher::MatcherConst::AtomName(name) => {
            let atom = ctx.atoms.intern(name);
            ctx.let_(Prim::Const(Const::Atom(atom)))
        }
        crate::matcher::MatcherConst::Bool(true) => ctx.let_(Prim::Const(Const::True)),
        crate::matcher::MatcherConst::Bool(false) => ctx.let_(Prim::Const(Const::False)),
        crate::matcher::MatcherConst::Nil => ctx.let_(Prim::Const(Const::Nil)),
        crate::matcher::MatcherConst::Utf8Binary(bytes) => {
            let bit_len = (bytes.len() * 8) as u64;
            let bs = ctx.let_(Prim::ConstBitstring(bytes.clone(), bit_len));
            ctx.let_(Prim::Brand(bs, "utf8".to_string()))
        }
        crate::matcher::MatcherConst::PreparedKey(index) => {
            let key = matcher.prepared_keys.get(*index as usize).ok_or_else(|| {
                LowerError::Unsupported {
                    span: Span::DUMMY,
                    what: format!("prepared matcher key {} is out of bounds", index),
                }
            })?;
            lower_matcher_const(ctx, matcher, key)?
        }
        crate::matcher::MatcherConst::EmptyList => {
            return Err(LowerError::Unsupported {
                span: Span::DUMMY,
                what: format!("matcher const {:?} cannot be materialized inline", value),
            });
        }
    })
}

pub(super) fn lower_matcher_pinned_var(
    ctx: &LowerCtx,
    matcher: &crate::matcher::Matcher,
    pinned: crate::matcher::PinnedId,
) -> Result<Var, LowerError> {
    let pinned = matcher
        .pinned
        .get(pinned.0 as usize)
        .ok_or_else(|| LowerError::Unsupported {
            span: Span::DUMMY,
            what: format!("matcher pinned slot {:?} out of bounds", pinned),
        })?;
    if let Some(input) = pinned.var
        && let Some(var) = matcher
            .inputs
            .get(input.0 as usize)
            .and_then(|input| input.var)
    {
        return Ok(var);
    }
    ctx.lookup(&pinned.name).ok_or_else(|| LowerError::Unbound {
        span: pinned.span,
        name: format!("pinned matcher var {}", pinned.name),
    })
}

pub(super) fn lower_matcher_bool_test(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    test: &crate::matcher::MatcherTest,
    state: &mut MatcherLowerState,
) -> Result<(Var, Vec<(crate::matcher::SubjectRef, Var)>), LowerError> {
    let mut true_values = Vec::new();
    let test_var = match test {
        crate::matcher::MatcherTest::EqConst { subject, value } => {
            let subject = materialize_matcher_subject(ctx, matcher, subject, state)?;
            match value {
                crate::matcher::MatcherConst::EmptyList => ctx.let_(Prim::IsEmptyList(subject)),
                _ => {
                    let lit = lower_matcher_const(ctx, matcher, value)?;
                    ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit))
                }
            }
        }
        crate::matcher::MatcherTest::EqPinned { subject, pinned } => {
            let subject = materialize_matcher_subject(ctx, matcher, subject, state)?;
            let pinned_var = lower_matcher_pinned_var(ctx, matcher, *pinned)?;
            ctx.let_(Prim::BinOp(BinOp::Eq, subject, pinned_var))
        }
        crate::matcher::MatcherTest::TupleArity { subject, arity } => {
            let subject = materialize_matcher_subject(ctx, matcher, subject, state)?;
            let tuple_ty = concrete_any_tuple(*arity as usize);
            ctx.let_(Prim::TypeTest(subject, Box::new(tuple_ty)))
        }
        crate::matcher::MatcherTest::ListCons { subject } => {
            let subject = materialize_matcher_subject(ctx, matcher, subject, state)?;
            let is_empty = ctx.let_(Prim::IsEmptyList(subject));
            let false_v = ctx.let_(Prim::Const(Const::False));
            ctx.let_(Prim::BinOp(BinOp::Eq, is_empty, false_v))
        }
        crate::matcher::MatcherTest::MapKind { subject } => {
            let subject = materialize_matcher_subject(ctx, matcher, subject, state)?;
            ctx.let_(Prim::TypeTest(subject, Box::new(concrete_any_map())))
        }
        crate::matcher::MatcherTest::Type { subject, ty } => {
            let subject = materialize_matcher_subject(ctx, matcher, subject, state)?;
            ctx.let_(Prim::TypeTest(subject, Box::new(ty.clone())))
        }
        crate::matcher::MatcherTest::MapHasKey { subject, key } => {
            let subject_ref = subject.clone();
            let subject = materialize_matcher_subject(ctx, matcher, subject, state)?;
            let key_var = lower_matcher_const(ctx, matcher, key)?;
            let value = ctx.let_(Prim::MatcherMapGet(subject, key_var));
            true_values.push((crate::matcher::map_value_subject(&subject_ref, key), value));
            let miss = ctx.let_(Prim::IsMatcherMapMiss(value));
            let false_v = ctx.let_(Prim::Const(Const::False));
            ctx.let_(Prim::BinOp(BinOp::Eq, miss, false_v))
        }
        crate::matcher::MatcherTest::Bitstring { .. } => {
            return Err(LowerError::Unsupported {
                span: Span::DUMMY,
                what: format!("matcher test {:?} needs specialized lowering", test),
            });
        }
    };
    Ok((test_var, true_values))
}

pub(super) fn lower_matcher_switch_test(
    ctx: &mut LowerCtx,
    subject: Var,
    kind: crate::matcher::SwitchKind,
    key: crate::matcher::SwitchKey,
) -> Result<Option<(Var, bool)>, LowerError> {
    Ok(Some(match (kind, key) {
        (crate::matcher::SwitchKind::TupleArity, crate::matcher::SwitchKey::Arity(arity)) => {
            let tuple_ty = concrete_any_tuple(arity as usize);
            (ctx.let_(Prim::TypeTest(subject, Box::new(tuple_ty))), true)
        }
        (crate::matcher::SwitchKind::Atom, crate::matcher::SwitchKey::AtomName(name)) => {
            let atom = ctx.atoms.intern(&name);
            let lit = ctx.let_(Prim::Const(Const::Atom(atom)));
            (ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit)), true)
        }
        (crate::matcher::SwitchKind::Int, crate::matcher::SwitchKey::Int(n)) => {
            let lit = ctx.let_(Prim::Const(Const::Int(n)));
            (ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit)), true)
        }
        (crate::matcher::SwitchKind::Float, crate::matcher::SwitchKey::FloatBits(bits)) => {
            let lit = ctx.let_(Prim::Const(Const::Float(f64::from_bits(bits))));
            (ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit)), true)
        }
        (crate::matcher::SwitchKind::Bool, crate::matcher::SwitchKey::Bool(b)) => {
            let lit = ctx.let_(Prim::Const(if b { Const::True } else { Const::False }));
            (ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit)), true)
        }
        (crate::matcher::SwitchKind::Nil, crate::matcher::SwitchKey::Nil)
        | (crate::matcher::SwitchKind::ListCons, crate::matcher::SwitchKey::Nil) => {
            let lit = ctx.let_(Prim::Const(Const::Nil));
            (ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit)), true)
        }
        (crate::matcher::SwitchKind::Binary, crate::matcher::SwitchKey::Utf8Binary(bytes)) => {
            let bit_len = (bytes.len() * 8) as u64;
            let bs = ctx.let_(Prim::ConstBitstring(bytes, bit_len));
            let lit = ctx.let_(Prim::Brand(bs, "utf8".to_string()));
            (ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit)), true)
        }
        (crate::matcher::SwitchKind::ListCons, crate::matcher::SwitchKey::EmptyList) => {
            (ctx.let_(Prim::IsEmptyList(subject)), true)
        }
        (crate::matcher::SwitchKind::ListCons, crate::matcher::SwitchKey::Cons) => {
            (ctx.let_(Prim::IsEmptyList(subject)), false)
        }
        _ => return Ok(None),
    }))
}

pub(super) fn lower_matcher_bitstring_test(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    subject: &crate::matcher::SubjectRef,
    fields: &[crate::matcher::MatcherBitField],
    success_block: BlockId,
    fail_block: BlockId,
    state: &mut MatcherLowerState,
) -> Result<(), LowerError> {
    let subject_v = materialize_matcher_subject(ctx, matcher, subject, state)?;
    let mut reader = ctx.let_(Prim::BitReaderInit(subject_v));
    for (index, field) in fields.iter().enumerate() {
        let size = lower_matcher_bit_size(ctx, &field.size, state)?;
        let result = ctx.let_(Prim::BitReadField {
            reader,
            ty: matcher_bit_type_to_ast(field.ty),
            size,
            endian: matcher_endian_to_ast(field.endian),
            signed: field.signed,
            unit: field.unit,
            is_last: index + 1 == fields.len(),
        });
        let ok = ctx.let_(Prim::TupleField(result, 0));
        let cont_b = ctx.cur_mut().block(vec![]);
        ctx.set_if_term(ok, cont_b, fail_block);
        ctx.cur_block = Some(cont_b);
        ctx.terminated = false;
        let extracted = ctx.let_(Prim::TupleField(result, 1));
        reader = ctx.let_(Prim::TupleField(result, 2));
        state
            .bitstring_fields
            .insert((subject.clone(), index as u32), extracted);
        for name in &field.direct_bindings {
            state.direct_bindings.insert(name.clone(), extracted);
        }
    }
    let done = ctx.let_(Prim::BitReaderDone(reader));
    ctx.set_if_term(done, success_block, fail_block);
    Ok(())
}

pub(super) fn lower_matcher_bit_size(
    ctx: &LowerCtx,
    size: &Option<crate::matcher::MatcherBitSize>,
    state: &MatcherLowerState,
) -> Result<Option<BitSizeIr>, LowerError> {
    Ok(match size {
        None => None,
        Some(crate::matcher::MatcherBitSize::Literal(n)) => Some(BitSizeIr::Literal(*n)),
        Some(crate::matcher::MatcherBitSize::BindingName(name)) => {
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

pub(super) fn lower_matcher_guard_expr(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    expr: &crate::matcher::GuardExpr,
    state: &mut MatcherLowerState,
) -> Result<Var, LowerError> {
    use crate::matcher::{GuardBinOp, GuardExpr, GuardUnaryOp};
    Ok(match expr {
        GuardExpr::Const(c) => lower_matcher_const(ctx, matcher, c)?,
        GuardExpr::Subject(subject) => materialize_matcher_subject(ctx, matcher, subject, state)?,
        GuardExpr::Pinned(pinned) => lower_matcher_pinned_var(ctx, matcher, *pinned)?,
        GuardExpr::Unary { op, expr } => {
            let v = lower_matcher_guard_expr(ctx, matcher, expr, state)?;
            match op {
                GuardUnaryOp::Not => ctx.let_(Prim::UnOp(UnOp::Not, v)),
                GuardUnaryOp::Neg => ctx.let_(Prim::UnOp(UnOp::Neg, v)),
            }
        }
        GuardExpr::Binary { op, lhs, rhs } => {
            let lhs = lower_matcher_guard_expr(ctx, matcher, lhs, state)?;
            let rhs = lower_matcher_guard_expr(ctx, matcher, rhs, state)?;
            let op = match op {
                GuardBinOp::Add => BinOp::Add,
                GuardBinOp::Sub => BinOp::Sub,
                GuardBinOp::Mul => BinOp::Mul,
                GuardBinOp::Div => BinOp::Div,
                GuardBinOp::Rem => BinOp::Mod,
                GuardBinOp::Eq => BinOp::Eq,
                GuardBinOp::Neq => BinOp::Neq,
                GuardBinOp::Lt => BinOp::Lt,
                GuardBinOp::LtEq => BinOp::Le,
                GuardBinOp::Gt => BinOp::Gt,
                GuardBinOp::GtEq => BinOp::Ge,
                GuardBinOp::And => BinOp::And,
                GuardBinOp::Or => BinOp::Or,
            };
            ctx.let_(Prim::BinOp(op, lhs, rhs))
        }
        GuardExpr::Dispatch { inputs, dispatch } => {
            lower_matcher_guard_dispatch(ctx, matcher, inputs, dispatch, state)?
        }
    })
}

pub(super) fn lower_matcher_guard_dispatch(
    ctx: &mut LowerCtx,
    outer_matcher: &crate::matcher::Matcher,
    inputs: &[crate::matcher::GuardExpr],
    dispatch: &crate::matcher::GuardDispatch,
    outer_state: &mut MatcherLowerState,
) -> Result<Var, LowerError> {
    if inputs.len() != dispatch.matcher.inputs.len() {
        return Err(LowerError::Unsupported {
            span: Span::DUMMY,
            what: format!(
                "guard dispatch input arity mismatch: {} args for {} inputs",
                inputs.len(),
                dispatch.matcher.inputs.len()
            ),
        });
    }

    let mut matcher = dispatch.matcher.clone();
    for (input, expr) in matcher.inputs.iter_mut().zip(inputs) {
        input.var = Some(lower_matcher_guard_expr(
            ctx,
            outer_matcher,
            expr,
            outer_state,
        )?);
    }

    let dispatch_block = ctx.cur_block;
    let dispatch_terminated = ctx.terminated;
    let result = ctx.cur_mut().fresh_var();
    let join_block = ctx.cur_mut().block(vec![result]);
    let fail_block = ctx.cur_mut().block(vec![]);
    ctx.cur_block = Some(fail_block);
    ctx.terminated = false;
    let false_v = ctx.let_(Prim::Const(Const::False));
    ctx.set_term(Term::Goto(join_block, vec![false_v]));

    ctx.cur_block = dispatch_block;
    ctx.terminated = dispatch_terminated;

    let mut state = MatcherLowerState::default();
    lower_guard_dispatch_node(
        ctx,
        &matcher,
        &dispatch.bodies,
        matcher.root,
        fail_block,
        join_block,
        &mut state,
    )?;
    ctx.cur_block = Some(join_block);
    ctx.terminated = false;
    Ok(result)
}

pub(super) fn lower_guard_dispatch_node(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    bodies: &[crate::matcher::GuardExpr],
    node_id: crate::matcher::NodeId,
    fail_block: BlockId,
    join_block: BlockId,
    state: &mut MatcherLowerState,
) -> Result<(), LowerError> {
    let Some(node) = matcher.node(node_id).cloned() else {
        return Err(LowerError::Unsupported {
            span: Span::DUMMY,
            what: format!("guard dispatch matcher node {:?} is out of bounds", node_id),
        });
    };
    match node {
        crate::matcher::MatcherNode::Fail { .. } => {
            if !ctx.terminated {
                ctx.set_term(Term::Goto(fail_block, vec![]));
            }
            Ok(())
        }
        crate::matcher::MatcherNode::Leaf(leaf) => {
            let body =
                bodies
                    .get(leaf.body_id as usize)
                    .ok_or_else(|| LowerError::Unsupported {
                        span: leaf.span,
                        what: format!("guard dispatch body {} is out of bounds", leaf.body_id),
                    })?;
            let value = lower_matcher_guard_expr(ctx, matcher, body, state)?;
            ctx.set_term(Term::Goto(join_block, vec![value]));
            ctx.terminated = true;
            Ok(())
        }
        crate::matcher::MatcherNode::Switch {
            subject,
            kind,
            cases,
            default,
            ..
        } => {
            let subject_v = materialize_matcher_subject(ctx, matcher, &subject, state)?;
            for (key, case) in cases {
                let Some((test, branch_on_true)) =
                    lower_matcher_switch_test(ctx, subject_v, kind.clone(), key)?
                else {
                    continue;
                };
                let (match_b, next_b) = if branch_on_true {
                    let next_b = ctx.cur_mut().block(vec![]);
                    let match_b = ctx.cur_mut().block(vec![]);
                    (match_b, next_b)
                } else {
                    let match_b = ctx.cur_mut().block(vec![]);
                    let next_b = ctx.cur_mut().block(vec![]);
                    (match_b, next_b)
                };
                if branch_on_true {
                    ctx.set_if_term(test, match_b, next_b);
                } else {
                    ctx.set_if_term(test, next_b, match_b);
                }
                ctx.cur_block = Some(match_b);
                ctx.terminated = false;
                let mut case_state = clone_matcher_lower_state(state);
                lower_guard_dispatch_node(
                    ctx,
                    matcher,
                    bodies,
                    case,
                    fail_block,
                    join_block,
                    &mut case_state,
                )?;
                ctx.cur_block = Some(next_b);
                ctx.terminated = false;
            }
            lower_guard_dispatch_node(ctx, matcher, bodies, default, fail_block, join_block, state)
        }
        crate::matcher::MatcherNode::Test {
            test,
            on_true,
            on_false,
            ..
        } => lower_guard_dispatch_test(
            ctx, matcher, bodies, test, on_true, on_false, fail_block, join_block, state,
        ),
        crate::matcher::MatcherNode::Guard {
            expr,
            on_true,
            on_false,
            ..
        } => {
            let guard = lower_matcher_guard_expr(ctx, matcher, &expr, state)?;
            let false_b = ctx.cur_mut().block(vec![]);
            let true_b = ctx.cur_mut().block(vec![]);
            ctx.set_if_term(guard, true_b, false_b);
            ctx.cur_block = Some(true_b);
            ctx.terminated = false;
            let mut true_state = clone_matcher_lower_state(state);
            lower_guard_dispatch_node(
                ctx,
                matcher,
                bodies,
                on_true,
                fail_block,
                join_block,
                &mut true_state,
            )?;
            ctx.cur_block = Some(false_b);
            ctx.terminated = false;
            lower_guard_dispatch_node(
                ctx, matcher, bodies, on_false, fail_block, join_block, state,
            )
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_guard_dispatch_test(
    ctx: &mut LowerCtx,
    matcher: &crate::matcher::Matcher,
    bodies: &[crate::matcher::GuardExpr],
    test: crate::matcher::MatcherTest,
    on_true: crate::matcher::NodeId,
    on_false: crate::matcher::NodeId,
    fail_block: BlockId,
    join_block: BlockId,
    state: &mut MatcherLowerState,
) -> Result<(), LowerError> {
    if let crate::matcher::MatcherTest::Bitstring { subject, fields } = test {
        let true_b = ctx.cur_mut().block(vec![]);
        let false_b = ctx.cur_mut().block(vec![]);
        let mut true_state = clone_matcher_lower_state(state);
        lower_matcher_bitstring_test(
            ctx,
            matcher,
            &subject,
            &fields,
            true_b,
            false_b,
            &mut true_state,
        )?;
        ctx.cur_block = Some(true_b);
        ctx.terminated = false;
        lower_guard_dispatch_node(
            ctx,
            matcher,
            bodies,
            on_true,
            fail_block,
            join_block,
            &mut true_state,
        )?;
        ctx.cur_block = Some(false_b);
        ctx.terminated = false;
        return lower_guard_dispatch_node(
            ctx, matcher, bodies, on_false, fail_block, join_block, state,
        );
    }

    let (test_var, true_values) = lower_matcher_bool_test(ctx, matcher, &test, state)?;
    let false_b = ctx.cur_mut().block(vec![]);
    let true_b = ctx.cur_mut().block(vec![]);
    ctx.set_if_term(test_var, true_b, false_b);
    ctx.cur_block = Some(true_b);
    ctx.terminated = false;
    let mut true_state = clone_matcher_lower_state(state);
    true_state.values.extend(true_values);
    lower_guard_dispatch_node(
        ctx,
        matcher,
        bodies,
        on_true,
        fail_block,
        join_block,
        &mut true_state,
    )?;
    ctx.cur_block = Some(false_b);
    ctx.terminated = false;
    lower_guard_dispatch_node(
        ctx, matcher, bodies, on_false, fail_block, join_block, state,
    )
}

pub(super) fn matcher_bit_type_to_ast(ty: crate::matcher::MatcherBitType) -> crate::ast::BitType {
    match ty {
        crate::matcher::MatcherBitType::Integer => crate::ast::BitType::Integer,
        crate::matcher::MatcherBitType::Float => crate::ast::BitType::Float,
        crate::matcher::MatcherBitType::Binary => crate::ast::BitType::Binary,
        crate::matcher::MatcherBitType::Bits => crate::ast::BitType::Bits,
        crate::matcher::MatcherBitType::Utf8 => crate::ast::BitType::Utf8,
        crate::matcher::MatcherBitType::Utf16 => crate::ast::BitType::Utf16,
        crate::matcher::MatcherBitType::Utf32 => crate::ast::BitType::Utf32,
    }
}

pub(super) fn matcher_endian_to_ast(endian: crate::matcher::MatcherEndian) -> crate::ast::Endian {
    match endian {
        crate::matcher::MatcherEndian::Big => crate::ast::Endian::Big,
        crate::matcher::MatcherEndian::Little => crate::ast::Endian::Little,
        crate::matcher::MatcherEndian::Native => crate::ast::Endian::Native,
    }
}
pub(super) fn lower_guard_helper_call_to_dispatch(
    ctx: &LowerCtx,
    name: &str,
    arity: usize,
    args: Vec<crate::matcher::GuardExpr>,
    stack: &mut Vec<(String, usize)>,
) -> Result<Option<crate::matcher::GuardExpr>, crate::pattern_matrix::PatternMatrixCompileError> {
    let key = (name.to_string(), arity);
    let Some(fn_def) = ctx.fn_defs_by_arity.get(&key) else {
        return Ok(None);
    };
    if stack.contains(&key) {
        return Err(crate::pattern_matrix::PatternMatrixCompileError::GuardCallCycle(key.0, key.1));
    }
    if fn_def.clauses.is_empty() {
        return Ok(None);
    }
    if fn_def
        .clauses
        .iter()
        .any(|clause| clause.params.len() != arity)
    {
        return Ok(None);
    }

    stack.push(key);
    let subjects: Vec<crate::fz_ir::Var> =
        (0..arity).map(|i| crate::fz_ir::Var(i as u32)).collect();
    let pattern_matrix = crate::pattern_matrix::PatternMatrix {
        subjects: subjects.clone(),
        rows: fn_def
            .clauses
            .iter()
            .enumerate()
            .map(|(i, clause)| crate::pattern_matrix::Row {
                patterns: clause.params.clone(),
                preconditions: Vec::new(),
                bindings: Vec::new(),
                guard: clause.guard.clone(),
                body_id: i as crate::pattern_matrix::BodyId,
            })
            .collect(),
    };
    let mut resolver =
        |callee: &str, callee_arity: usize, callee_args: Vec<crate::matcher::GuardExpr>| {
            lower_guard_helper_call_to_dispatch(ctx, callee, callee_arity, callee_args, stack)
        };
    let matcher_result = crate::pattern_matrix::compile_pattern_matrix_with_guard_resolver(
        pattern_matrix,
        &mut resolver,
    );
    stack.pop();
    let mut matcher = matcher_result?;
    let param_input_by_name: HashMap<String, crate::fz_ir::Var> = fn_def.clauses[0]
        .params
        .iter()
        .enumerate()
        .filter_map(|(i, pattern)| match &pattern.node {
            crate::ast::Pattern::Var(name) => Some((name.clone(), crate::fz_ir::Var(i as u32))),
            _ => None,
        })
        .collect();
    for pinned in &mut matcher.pinned {
        if let Some(input) = param_input_by_name.get(&pinned.name) {
            pinned.var = Some(*input);
        }
    }

    let mut pinned_by_name: HashMap<String, crate::matcher::PinnedId> = matcher
        .pinned
        .iter()
        .enumerate()
        .map(|(i, pinned)| (pinned.name.clone(), crate::matcher::PinnedId(i as u32)))
        .collect();
    for clause in &fn_def.clauses {
        let mut bound = std::collections::BTreeSet::new();
        for pattern in &clause.params {
            let mut names = Vec::new();
            collect_pattern_bound_names(&pattern.node, &mut names);
            bound.extend(names);
        }
        let mut captures = Vec::new();
        crate::pattern_matrix::collect_guard_capture_names(
            &clause.body.node,
            &bound,
            &mut captures,
        );
        for capture in captures {
            if let std::collections::hash_map::Entry::Vacant(entry) = pinned_by_name.entry(capture)
            {
                let id = crate::matcher::PinnedId(matcher.pinned.len() as u32);
                matcher.pinned.push(crate::matcher::PinnedInput {
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
        let bindings = crate::pattern_matrix::collect_matcher_pattern_bindings(
            &clause.params,
            &pinned_by_name,
        )?;
        let mut resolver =
            |callee: &str, callee_arity: usize, callee_args: Vec<crate::matcher::GuardExpr>| {
                lower_guard_helper_call_to_dispatch(ctx, callee, callee_arity, callee_args, stack)
            };
        bodies.push(crate::pattern_matrix::compile_guard_expr_subset(
            &clause.body.node,
            &bindings,
            &pinned_by_name,
            &mut resolver,
        )?);
    }

    Ok(Some(crate::matcher::GuardExpr::Dispatch {
        inputs: args,
        dispatch: Box::new(crate::matcher::GuardDispatch { matcher, bodies }),
    }))
}

pub(super) fn collect_matcher_pinned_names_recursive(
    matcher: &crate::matcher::Matcher,
    out: &mut Vec<String>,
) {
    for pinned in &matcher.pinned {
        if pinned.var.is_some() {
            continue;
        }
        if !out.contains(&pinned.name) {
            out.push(pinned.name.clone());
        }
    }
    for node in &matcher.nodes {
        if let crate::matcher::MatcherNode::Guard { expr, .. } = node {
            collect_guard_expr_dispatch_pinned(expr, out);
        }
    }
}

pub(super) fn collect_guard_expr_dispatch_pinned(expr: &crate::matcher::GuardExpr, out: &mut Vec<String>) {
    match expr {
        crate::matcher::GuardExpr::Unary { expr, .. } => {
            collect_guard_expr_dispatch_pinned(expr, out);
        }
        crate::matcher::GuardExpr::Binary { lhs, rhs, .. } => {
            collect_guard_expr_dispatch_pinned(lhs, out);
            collect_guard_expr_dispatch_pinned(rhs, out);
        }
        crate::matcher::GuardExpr::Dispatch { inputs, dispatch } => {
            for input in inputs {
                collect_guard_expr_dispatch_pinned(input, out);
            }
            collect_matcher_pinned_names_recursive(&dispatch.matcher, out);
            for body in &dispatch.bodies {
                collect_guard_expr_dispatch_pinned(body, out);
            }
        }
        crate::matcher::GuardExpr::Const(_)
        | crate::matcher::GuardExpr::Subject(_)
        | crate::matcher::GuardExpr::Pinned(_) => {}
    }
}

pub(super) fn materialize_prepared_matcher_key(
    ctx: &mut LowerCtx,
    key: &crate::matcher::MatcherConst,
) -> Result<Var, LowerError> {
    match key {
        crate::matcher::MatcherConst::FloatBits(bits) => {
            Ok(ctx.let_(Prim::Const(Const::Float(f64::from_bits(*bits)))))
        }
        crate::matcher::MatcherConst::Utf8Binary(bytes) => {
            let bit_len = (bytes.len() * 8) as u64;
            let bs = ctx.let_(Prim::ConstBitstring(bytes.clone(), bit_len));
            Ok(ctx.let_(Prim::Brand(bs, "utf8".to_string())))
        }
        crate::matcher::MatcherConst::AtomName(name) => {
            let atom = ctx.atoms.intern(name);
            Ok(ctx.let_(Prim::Const(Const::Atom(atom))))
        }
        crate::matcher::MatcherConst::Int(n) => Ok(ctx.let_(Prim::Const(Const::Int(*n)))),
        crate::matcher::MatcherConst::Bool(true) => Ok(ctx.let_(Prim::Const(Const::True))),
        crate::matcher::MatcherConst::Bool(false) => Ok(ctx.let_(Prim::Const(Const::False))),
        crate::matcher::MatcherConst::Nil => Ok(ctx.let_(Prim::Const(Const::Nil))),
        crate::matcher::MatcherConst::EmptyList | crate::matcher::MatcherConst::PreparedKey(_) => {
            Err(LowerError::Unsupported {
                span: Span::DUMMY,
                what: format!("matcher prepared key {:?} cannot be materialized", key),
            })
        }
    }
}
