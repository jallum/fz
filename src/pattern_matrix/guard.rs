use crate::ast::{Expr, Spanned};
use crate::fz_ir::Var;

use super::pattern_ops::push_matcher_node;
use super::PatternMatrixCompileError;

pub(crate) fn preconditions_to_matcher_nodes(
    preconditions: &[(Var, crate::types::Ty)],
    input_by_var: &std::collections::HashMap<Var, crate::matcher::InputId>,
    on_true: crate::matcher::NodeId,
    on_false: Option<crate::matcher::NodeId>,
    nodes: &mut Vec<crate::matcher::MatcherNode>,
) -> Result<crate::matcher::NodeId, PatternMatrixCompileError> {
    if preconditions.is_empty() {
        return Ok(on_true);
    }
    let on_false = on_false.unwrap_or_else(|| {
        push_matcher_node(
            nodes,
            crate::matcher::MatcherNode::Fail {
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
            crate::matcher::MatcherNode::Test {
                test: crate::matcher::MatcherTest::Type {
                    subject: crate::matcher::SubjectRef::Input(input),
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
    bindings: &[crate::matcher::MatcherBinding],
    pinned_by_name: &std::collections::HashMap<String, crate::matcher::PinnedId>,
    on_true: crate::matcher::NodeId,
    on_false: Option<crate::matcher::NodeId>,
    nodes: &mut Vec<crate::matcher::MatcherNode>,
    _prepared_keys: &mut Vec<crate::matcher::MatcherConst>,
    guard_call_resolver: &mut impl FnMut(
        &str,
        usize,
        Vec<crate::matcher::GuardExpr>,
    ) -> Result<
        Option<crate::matcher::GuardExpr>,
        PatternMatrixCompileError,
    >,
) -> Result<crate::matcher::NodeId, PatternMatrixCompileError> {
    let Some(guard) = guard else {
        return Ok(on_true);
    };
    let on_false = on_false.unwrap_or_else(|| {
        push_matcher_node(
            nodes,
            crate::matcher::MatcherNode::Fail {
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
        crate::matcher::MatcherNode::Guard {
            expr,
            on_true,
            on_false,
            span: guard.span,
        },
    ))
}

pub(crate) fn guard_expr_to_matcher(
    expr: &Expr,
    bindings: &std::collections::HashMap<String, crate::matcher::SubjectRef>,
    pinned_by_name: &std::collections::HashMap<String, crate::matcher::PinnedId>,
    guard_call_resolver: &mut impl FnMut(
        &str,
        usize,
        Vec<crate::matcher::GuardExpr>,
    ) -> Result<
        Option<crate::matcher::GuardExpr>,
        PatternMatrixCompileError,
    >,
) -> Result<crate::matcher::GuardExpr, PatternMatrixCompileError> {
    use crate::ast::{BinOp, Expr, UnOp};
    Ok(match expr {
        Expr::Int(n) => crate::matcher::GuardExpr::Const(crate::matcher::MatcherConst::Int(*n)),
        Expr::Float(n) => {
            crate::matcher::GuardExpr::Const(crate::matcher::MatcherConst::FloatBits(n.to_bits()))
        }
        Expr::Binary(bytes) => crate::matcher::GuardExpr::Const(
            crate::matcher::MatcherConst::Utf8Binary(bytes.clone()),
        ),
        Expr::Atom(name) => {
            crate::matcher::GuardExpr::Const(crate::matcher::MatcherConst::AtomName(name.clone()))
        }
        Expr::Bool(b) => crate::matcher::GuardExpr::Const(crate::matcher::MatcherConst::Bool(*b)),
        Expr::Nil => crate::matcher::GuardExpr::Const(crate::matcher::MatcherConst::Nil),
        Expr::Var(name) => {
            if let Some(subject) = bindings.get(name) {
                crate::matcher::GuardExpr::Subject(subject.clone())
            } else if let Some(pinned) = pinned_by_name.get(name) {
                crate::matcher::GuardExpr::Pinned(*pinned)
            } else {
                return Err(PatternMatrixCompileError::UnknownGuardVar(name.clone()));
            }
        }
        Expr::UnOp(UnOp::Not, a) => crate::matcher::GuardExpr::Unary {
            op: crate::matcher::GuardUnaryOp::Not,
            expr: Box::new(guard_expr_to_matcher(
                &a.node,
                bindings,
                pinned_by_name,
                guard_call_resolver,
            )?),
        },
        Expr::UnOp(UnOp::Neg, a) => crate::matcher::GuardExpr::Unary {
            op: crate::matcher::GuardUnaryOp::Neg,
            expr: Box::new(guard_expr_to_matcher(
                &a.node,
                bindings,
                pinned_by_name,
                guard_call_resolver,
            )?),
        },
        Expr::BinOp(op, a, b) => crate::matcher::GuardExpr::Binary {
            op: match op {
                BinOp::Add => crate::matcher::GuardBinOp::Add,
                BinOp::Sub => crate::matcher::GuardBinOp::Sub,
                BinOp::Mul => crate::matcher::GuardBinOp::Mul,
                BinOp::Div => crate::matcher::GuardBinOp::Div,
                BinOp::Rem => crate::matcher::GuardBinOp::Rem,
                BinOp::Eq => crate::matcher::GuardBinOp::Eq,
                BinOp::Neq => crate::matcher::GuardBinOp::Neq,
                BinOp::Lt => crate::matcher::GuardBinOp::Lt,
                BinOp::LtEq => crate::matcher::GuardBinOp::LtEq,
                BinOp::Gt => crate::matcher::GuardBinOp::Gt,
                BinOp::GtEq => crate::matcher::GuardBinOp::GtEq,
                BinOp::And => crate::matcher::GuardBinOp::And,
                BinOp::Or => crate::matcher::GuardBinOp::Or,
                BinOp::Pipe | BinOp::Cons => {
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
    bindings: &[crate::matcher::MatcherBinding],
    pinned_by_name: &std::collections::HashMap<String, crate::matcher::PinnedId>,
    guard_call_resolver: &mut F,
) -> Result<crate::matcher::GuardExpr, PatternMatrixCompileError>
where
    F: FnMut(
        &str,
        usize,
        Vec<crate::matcher::GuardExpr>,
    ) -> Result<Option<crate::matcher::GuardExpr>, PatternMatrixCompileError>,
{
    let mut bound = std::collections::HashMap::new();
    for binding in bindings {
        bound.insert(binding.name.clone(), binding.source.clone());
    }
    guard_expr_to_matcher(expr, &bound, pinned_by_name, guard_call_resolver)
}
