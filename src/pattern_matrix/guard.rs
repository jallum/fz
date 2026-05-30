use crate::ast::{Expr, Spanned};
use crate::fz_ir::Var;

use super::PatternMatrixCompileError;
use super::pattern_ops::push_matcher_node;

pub(crate) fn preconditions_to_matcher_nodes(
    preconditions: &[(Var, crate::types::Ty)],
    input_by_var: &std::collections::HashMap<Var, crate::exec::matcher::InputId>,
    on_true: crate::exec::matcher::NodeId,
    on_false: Option<crate::exec::matcher::NodeId>,
    nodes: &mut Vec<crate::exec::matcher::MatcherNode>,
) -> Result<crate::exec::matcher::NodeId, PatternMatrixCompileError> {
    if preconditions.is_empty() {
        return Ok(on_true);
    }
    let on_false = on_false.unwrap_or_else(|| {
        push_matcher_node(
            nodes,
            crate::exec::matcher::MatcherNode::Fail {
                span: crate::diag::Span::DUMMY,
            },
        )
    });
    let mut current = on_true;
    for (var, ty) in preconditions.iter().rev() {
        let input = input_by_var
            .get(var)
            .copied()
            .ok_or(PatternMatrixCompileError::UnknownSubject(*var))?;
        current = push_matcher_node(
            nodes,
            crate::exec::matcher::MatcherNode::Test {
                test: crate::exec::matcher::MatcherTest::Type {
                    subject: crate::exec::matcher::SubjectRef::Input(input),
                    ty: ty.clone(),
                },
                on_true: current,
                on_false,
                span: crate::diag::Span::DUMMY,
            },
        );
    }
    Ok(current)
}

pub(crate) fn guard_to_matcher_node(
    guard: Option<&Spanned<Expr>>,
    bindings: &[crate::exec::matcher::MatcherBinding],
    pinned_by_name: &std::collections::HashMap<String, crate::exec::matcher::PinnedId>,
    on_true: crate::exec::matcher::NodeId,
    on_false: Option<crate::exec::matcher::NodeId>,
    nodes: &mut Vec<crate::exec::matcher::MatcherNode>,
    _prepared_keys: &mut Vec<crate::exec::matcher::MatcherConst>,
    guard_call_resolver: &mut impl FnMut(
        &str,
        usize,
        Vec<crate::exec::matcher::GuardExpr>,
    ) -> Result<
        Option<crate::exec::matcher::GuardExpr>,
        PatternMatrixCompileError,
    >,
) -> Result<crate::exec::matcher::NodeId, PatternMatrixCompileError> {
    let Some(guard) = guard else {
        return Ok(on_true);
    };
    let on_false = on_false.unwrap_or_else(|| {
        push_matcher_node(
            nodes,
            crate::exec::matcher::MatcherNode::Fail {
                span: crate::diag::Span::DUMMY,
            },
        )
    });
    let mut bound = std::collections::HashMap::new();
    for binding in bindings {
        bound.insert(binding.name.clone(), binding.source.clone());
    }
    let expr = guard_expr_to_matcher(&guard.node, &bound, pinned_by_name, guard_call_resolver)?;
    Ok(push_matcher_node(
        nodes,
        crate::exec::matcher::MatcherNode::Guard {
            expr,
            on_true,
            on_false,
            span: guard.span,
        },
    ))
}

pub(crate) fn guard_expr_to_matcher(
    expr: &Expr,
    bindings: &std::collections::HashMap<String, crate::exec::matcher::SubjectRef>,
    pinned_by_name: &std::collections::HashMap<String, crate::exec::matcher::PinnedId>,
    guard_call_resolver: &mut impl FnMut(
        &str,
        usize,
        Vec<crate::exec::matcher::GuardExpr>,
    ) -> Result<
        Option<crate::exec::matcher::GuardExpr>,
        PatternMatrixCompileError,
    >,
) -> Result<crate::exec::matcher::GuardExpr, PatternMatrixCompileError> {
    use crate::ast::{BinOp, Expr, UnOp};
    Ok(match expr {
        Expr::Int(n) => {
            crate::exec::matcher::GuardExpr::Const(crate::exec::matcher::MatcherConst::Int(*n))
        }
        Expr::Float(n) => crate::exec::matcher::GuardExpr::Const(
            crate::exec::matcher::MatcherConst::FloatBits(n.to_bits()),
        ),
        Expr::Binary(bytes) => crate::exec::matcher::GuardExpr::Const(
            crate::exec::matcher::MatcherConst::Utf8Binary(bytes.clone()),
        ),
        Expr::Atom(name) => crate::exec::matcher::GuardExpr::Const(
            crate::exec::matcher::MatcherConst::AtomName(name.clone()),
        ),
        Expr::Bool(b) => {
            crate::exec::matcher::GuardExpr::Const(crate::exec::matcher::MatcherConst::Bool(*b))
        }
        Expr::Nil => {
            crate::exec::matcher::GuardExpr::Const(crate::exec::matcher::MatcherConst::Nil)
        }
        Expr::Var(name) => {
            if let Some(subject) = bindings.get(name) {
                crate::exec::matcher::GuardExpr::Subject(subject.clone())
            } else if let Some(pinned) = pinned_by_name.get(name) {
                crate::exec::matcher::GuardExpr::Pinned(*pinned)
            } else {
                return Err(PatternMatrixCompileError::UnknownGuardVar(name.clone()));
            }
        }
        Expr::Ascribe(inner, _) => {
            guard_expr_to_matcher(&inner.node, bindings, pinned_by_name, guard_call_resolver)?
        }
        Expr::UnOp(UnOp::Not, a) => crate::exec::matcher::GuardExpr::Unary {
            op: crate::exec::matcher::GuardUnaryOp::Not,
            expr: Box::new(guard_expr_to_matcher(
                &a.node,
                bindings,
                pinned_by_name,
                guard_call_resolver,
            )?),
        },
        Expr::UnOp(UnOp::Neg, a) => crate::exec::matcher::GuardExpr::Unary {
            op: crate::exec::matcher::GuardUnaryOp::Neg,
            expr: Box::new(guard_expr_to_matcher(
                &a.node,
                bindings,
                pinned_by_name,
                guard_call_resolver,
            )?),
        },
        Expr::BinOp(op, a, b) => crate::exec::matcher::GuardExpr::Binary {
            op: match op {
                BinOp::Add => crate::exec::matcher::GuardBinOp::Add,
                BinOp::Sub => crate::exec::matcher::GuardBinOp::Sub,
                BinOp::Mul => crate::exec::matcher::GuardBinOp::Mul,
                BinOp::Div => crate::exec::matcher::GuardBinOp::Div,
                BinOp::Rem => crate::exec::matcher::GuardBinOp::Rem,
                BinOp::Eq => crate::exec::matcher::GuardBinOp::Eq,
                BinOp::Neq => crate::exec::matcher::GuardBinOp::Neq,
                BinOp::Lt => crate::exec::matcher::GuardBinOp::Lt,
                BinOp::LtEq => crate::exec::matcher::GuardBinOp::LtEq,
                BinOp::Gt => crate::exec::matcher::GuardBinOp::Gt,
                BinOp::GtEq => crate::exec::matcher::GuardBinOp::GtEq,
                BinOp::And => crate::exec::matcher::GuardBinOp::And,
                BinOp::Or => crate::exec::matcher::GuardBinOp::Or,
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
                Expr::FnRef { name, arity } if *arity == args.len() => {
                    Some((name.as_str(), *arity))
                }
                _ => None,
            };
            let Some((name, arity)) = callee else {
                return Err(PatternMatrixCompileError::UnsupportedGuardExpr);
            };
            let args = args
                .iter()
                .map(|arg| {
                    guard_expr_to_matcher(&arg.node, bindings, pinned_by_name, guard_call_resolver)
                })
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
    bindings: &[crate::exec::matcher::MatcherBinding],
    pinned_by_name: &std::collections::HashMap<String, crate::exec::matcher::PinnedId>,
    guard_call_resolver: &mut F,
) -> Result<crate::exec::matcher::GuardExpr, PatternMatrixCompileError>
where
    F: FnMut(
        &str,
        usize,
        Vec<crate::exec::matcher::GuardExpr>,
    ) -> Result<Option<crate::exec::matcher::GuardExpr>, PatternMatrixCompileError>,
{
    let mut bound = std::collections::HashMap::new();
    for binding in bindings {
        bound.insert(binding.name.clone(), binding.source.clone());
    }
    guard_expr_to_matcher(expr, &bound, pinned_by_name, guard_call_resolver)
}
