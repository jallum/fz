use crate::ast::{BinOp, Expr, Spanned, UnOp};
use crate::diag::Span;
use crate::exec::matcher::{
    GuardBinOp, GuardExpr, GuardUnaryOp, InputId, MatcherBinding, MatcherConst, MatcherNode, MatcherTest, NodeId,
    PinnedId, SubjectRef,
};
use crate::fz_ir::Var;
use crate::types::Ty;
use std::collections::HashMap;

use super::PatternMatrixCompileError;
use super::pattern_ops::push_matcher_node;

pub(crate) fn preconditions_to_matcher_nodes(
    preconditions: &[(Var, Ty)],
    input_by_var: &HashMap<Var, InputId>,
    on_true: NodeId,
    on_false: Option<NodeId>,
    nodes: &mut Vec<MatcherNode>,
) -> Result<NodeId, PatternMatrixCompileError> {
    if preconditions.is_empty() {
        return Ok(on_true);
    }
    let on_false = on_false.unwrap_or_else(|| push_matcher_node(nodes, MatcherNode::Fail { span: Span::DUMMY }));
    let mut current = on_true;
    for (var, ty) in preconditions.iter().rev() {
        let input = input_by_var
            .get(var)
            .copied()
            .ok_or(PatternMatrixCompileError::UnknownSubject(*var))?;
        current = push_matcher_node(
            nodes,
            MatcherNode::Test {
                test: MatcherTest::Type {
                    subject: SubjectRef::Input(input),
                    ty: ty.clone(),
                },
                on_true: current,
                on_false,
                span: Span::DUMMY,
            },
        );
    }
    Ok(current)
}

pub(crate) fn guard_to_matcher_node(
    guard: Option<&Spanned<Expr>>,
    bindings: &[MatcherBinding],
    pinned_by_name: &HashMap<String, PinnedId>,
    on_true: NodeId,
    on_false: Option<NodeId>,
    nodes: &mut Vec<MatcherNode>,
    _prepared_keys: &mut Vec<MatcherConst>,
    guard_call_resolver: &mut impl FnMut(
        &str,
        usize,
        Vec<GuardExpr>,
    ) -> Result<Option<GuardExpr>, PatternMatrixCompileError>,
) -> Result<NodeId, PatternMatrixCompileError> {
    let Some(guard) = guard else {
        return Ok(on_true);
    };
    let on_false = on_false.unwrap_or_else(|| push_matcher_node(nodes, MatcherNode::Fail { span: Span::DUMMY }));
    let mut bound = HashMap::new();
    for binding in bindings {
        bound.insert(binding.name.clone(), binding.source.clone());
    }
    let expr = guard_expr_to_matcher(&guard.node, &bound, pinned_by_name, guard_call_resolver)?;
    Ok(push_matcher_node(
        nodes,
        MatcherNode::Guard {
            expr,
            on_true,
            on_false,
            span: guard.span,
        },
    ))
}

pub(crate) fn guard_expr_to_matcher(
    expr: &Expr,
    bindings: &HashMap<String, SubjectRef>,
    pinned_by_name: &HashMap<String, PinnedId>,
    guard_call_resolver: &mut impl FnMut(
        &str,
        usize,
        Vec<GuardExpr>,
    ) -> Result<Option<GuardExpr>, PatternMatrixCompileError>,
) -> Result<GuardExpr, PatternMatrixCompileError> {
    Ok(match expr {
        Expr::Int(n) => GuardExpr::Const(MatcherConst::Int(*n)),
        Expr::Float(n) => GuardExpr::Const(MatcherConst::FloatBits(n.to_bits())),
        Expr::Binary(bytes) => GuardExpr::Const(MatcherConst::Utf8Binary(bytes.clone())),
        Expr::Atom(name) => GuardExpr::Const(MatcherConst::AtomName(name.clone())),
        Expr::Bool(b) => GuardExpr::Const(MatcherConst::Bool(*b)),
        Expr::Nil => GuardExpr::Const(MatcherConst::Nil),
        Expr::Var(name) => {
            if let Some(subject) = bindings.get(name) {
                GuardExpr::Subject(subject.clone())
            } else if let Some(pinned) = pinned_by_name.get(name) {
                GuardExpr::Pinned(*pinned)
            } else {
                return Err(PatternMatrixCompileError::UnknownGuardVar(name.clone()));
            }
        }
        Expr::Ascribe(inner, _) => guard_expr_to_matcher(&inner.node, bindings, pinned_by_name, guard_call_resolver)?,
        Expr::UnOp(UnOp::Not, a) => GuardExpr::Unary {
            op: GuardUnaryOp::Not,
            expr: Box::new(guard_expr_to_matcher(
                &a.node,
                bindings,
                pinned_by_name,
                guard_call_resolver,
            )?),
        },
        Expr::UnOp(UnOp::Neg, a) => GuardExpr::Unary {
            op: GuardUnaryOp::Neg,
            expr: Box::new(guard_expr_to_matcher(
                &a.node,
                bindings,
                pinned_by_name,
                guard_call_resolver,
            )?),
        },
        Expr::BinOp(op, a, b) => GuardExpr::Binary {
            op: match op {
                BinOp::Add => GuardBinOp::Add,
                BinOp::Sub => GuardBinOp::Sub,
                BinOp::Mul => GuardBinOp::Mul,
                BinOp::Div => GuardBinOp::Div,
                BinOp::Rem => GuardBinOp::Rem,
                BinOp::Eq => GuardBinOp::Eq,
                BinOp::Neq => GuardBinOp::Neq,
                BinOp::Lt => GuardBinOp::Lt,
                BinOp::LtEq => GuardBinOp::LtEq,
                BinOp::Gt => GuardBinOp::Gt,
                BinOp::GtEq => GuardBinOp::GtEq,
                BinOp::And => GuardBinOp::And,
                BinOp::Or => GuardBinOp::Or,
                BinOp::Pipe
                | BinOp::Cons
                | BinOp::ListConcat
                | BinOp::ListSubtract
                | BinOp::BinConcat
                | BinOp::Range
                | BinOp::RangeStep
                | BinOp::In
                | BinOp::NotIn => {
                    return Err(PatternMatrixCompileError::UnsupportedGuardExpr);
                }
            },
            lhs: Box::new(guard_expr_to_matcher(
                &a.node,
                bindings,
                pinned_by_name,
                guard_call_resolver,
            )?),
            rhs: Box::new(guard_expr_to_matcher(
                &b.node,
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
                return Err(PatternMatrixCompileError::UnsupportedGuardExpr);
            };
            let args = args
                .iter()
                .map(|arg| guard_expr_to_matcher(&arg.node, bindings, pinned_by_name, guard_call_resolver))
                .collect::<Result<Vec<_>, _>>()?;
            match guard_call_resolver(name, arity, args)? {
                Some(expr) => expr,
                None => return Err(PatternMatrixCompileError::UnsupportedGuardExpr),
            }
        }
        _ => return Err(PatternMatrixCompileError::UnsupportedGuardExpr),
    })
}

pub fn compile_guard_expr_subset<F>(
    expr: &Expr,
    bindings: &[MatcherBinding],
    pinned_by_name: &HashMap<String, PinnedId>,
    guard_call_resolver: &mut F,
) -> Result<GuardExpr, PatternMatrixCompileError>
where
    F: FnMut(&str, usize, Vec<GuardExpr>) -> Result<Option<GuardExpr>, PatternMatrixCompileError>,
{
    let mut bound = HashMap::new();
    for binding in bindings {
        bound.insert(binding.name.clone(), binding.source.clone());
    }
    guard_expr_to_matcher(expr, &bound, pinned_by_name, guard_call_resolver)
}
