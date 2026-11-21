//! A guard helper planned at the literals a call hands it.
//!
//! `is_function(f, 2)` passes a literal where `is_function(f)` passes nothing
//! but variables, and the literal decides most of the helper's clauses: the two
//! that raise for a bad arity cannot win for `2`. Substituting the literal for
//! its parameter and deciding each clause's guard on constants leaves the
//! clauses that can still win, and what is left of `is_function/2` is a type
//! test on its first argument.
//!
//! A clause is decided only when every name its guard and body read is a
//! literal or a variable of its own, and the guard is built from the forms
//! below. A clause the substitution cannot read stays as it is: specialising
//! never drops a clause it did not decide.

use super::{GuardCallee, PatternResolver, SourcePatternError};
use crate::ast::{BinOp, Callee, Expr, FnClause, Pattern, Spanned, UnOp, Var};
use crate::fast_hash::HashMap;
use crate::function_surface::CallableSurface;
use crate::ground_value::GroundValue;

/// The value a guard writes as a literal: an integer, a float or an atom.
pub(crate) fn literal_of(expr: &Expr) -> Option<GroundValue> {
    match expr {
        Expr::Int(value) => Some(GroundValue::Int(*value)),
        Expr::Float(value) => Some(GroundValue::Float(value.to_bits())),
        Expr::Atom(name) => Some(GroundValue::Atom(name.clone())),
        Expr::Bool(value) => Some(GroundValue::Bool(*value)),
        Expr::Nil => Some(GroundValue::Nil),
        _ => None,
    }
}

fn literal_expr(value: &GroundValue) -> Expr {
    match value {
        GroundValue::Int(value) => Expr::Int(*value),
        GroundValue::Float(bits) => Expr::Float(f64::from_bits(*bits)),
        GroundValue::Atom(name) => Expr::Atom(name.clone()),
        GroundValue::Bool(value) => Expr::Bool(*value),
        GroundValue::Nil => Expr::Nil,
        GroundValue::Binary(bytes) | GroundValue::Utf8Binary(bytes) => Expr::Binary(bytes.clone()),
    }
}

/// The clauses of a helper that can still win when its arguments at the
/// literal positions are those literals, or `None` when nothing was decided
/// and the helper stands as it is.
pub(crate) fn clauses_at_literals<TypeHandle>(
    surface: &impl CallableSurface,
    literals: &[Option<GroundValue>],
    resolver: &mut impl PatternResolver<TypeHandle>,
) -> Result<Option<Vec<FnClause>>, SourcePatternError> {
    let mut residue = Vec::with_capacity(surface.clauses().len());
    let mut decided = false;
    for clause in surface.clauses() {
        match clause_at_literals(clause, literals, resolver)? {
            ClauseAtLiterals::Dropped => decided = true,
            ClauseAtLiterals::Specialised(clause) => {
                decided = true;
                residue.push(*clause);
            }
            ClauseAtLiterals::Unchanged => residue.push(clause.clone()),
        }
    }
    Ok(decided.then_some(residue))
}

enum ClauseAtLiterals {
    /// Its guard fails for these literals: the clause cannot win.
    Dropped,
    /// The literals substituted, and its guard decided where the literals
    /// decide it.
    Specialised(Box<FnClause>),
    Unchanged,
}

fn clause_at_literals<TypeHandle>(
    clause: &FnClause,
    literals: &[Option<GroundValue>],
    resolver: &mut impl PatternResolver<TypeHandle>,
) -> Result<ClauseAtLiterals, SourcePatternError> {
    let Some(bound) = bind_literal_parameters(clause, literals) else {
        return Ok(ClauseAtLiterals::Unchanged);
    };
    if bound.is_empty() {
        return Ok(ClauseAtLiterals::Unchanged);
    }
    let guard = match &clause.guard {
        Some(guard) => match substitute(guard, &bound) {
            Some(guard) => Some(guard),
            None => return Ok(ClauseAtLiterals::Unchanged),
        },
        None => None,
    };
    let guard = match guard {
        Some(guard) => match decide(&guard.node, resolver)? {
            Some(true) => None,
            Some(false) => return Ok(ClauseAtLiterals::Dropped),
            None => Some(guard),
        },
        None => None,
    };
    let Some(body) = substitute(&clause.body, &bound) else {
        return Ok(ClauseAtLiterals::Unchanged);
    };
    let params = clause
        .params
        .iter()
        .map(|param| match &param.node {
            Pattern::Var(name) if bound.contains_key(name) => Spanned::new(Pattern::Wildcard, param.span),
            _ => param.clone(),
        })
        .collect();
    Ok(ClauseAtLiterals::Specialised(Box::new(FnClause {
        params,
        guard,
        body,
        ..clause.clone()
    })))
}

/// The name each literal position's parameter binds to its literal. `None`
/// when a parameter at a literal position is anything but a plain, unannotated
/// variable or `_`: a pattern is not decided here.
fn bind_literal_parameters(clause: &FnClause, literals: &[Option<GroundValue>]) -> Option<HashMap<Var, Expr>> {
    let mut bound = HashMap::default();
    for (position, literal) in literals.iter().enumerate() {
        let Some(literal) = literal else {
            continue;
        };
        match (&clause.params[position].node, &clause.param_annotations[position]) {
            (Pattern::Wildcard, None) => {}
            (Pattern::Var(name), None) => {
                bound.insert(name.clone(), literal_expr(literal));
            }
            _ => return None,
        }
    }
    Some(bound)
}

/// `expr` with each bound name replaced by its literal, or `None` when it
/// holds a form a guard decision does not read.
fn substitute(expr: &Spanned<Expr>, bound: &HashMap<Var, Expr>) -> Option<Spanned<Expr>> {
    let node = match &expr.node {
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Binary(_)
        | Expr::Atom(_)
        | Expr::Bool(_)
        | Expr::Nil
        | Expr::Alias(_) => expr.node.clone(),
        Expr::Var(name) => bound.get(name).cloned().unwrap_or_else(|| expr.node.clone()),
        Expr::Ascribe(inner, ty) => Expr::Ascribe(Box::new(substitute(inner, bound)?), ty.clone()),
        Expr::UnOp(op, arg) => Expr::UnOp(*op, Box::new(substitute(arg, bound)?)),
        Expr::BinOp(op, lhs, rhs) => Expr::BinOp(
            *op,
            Box::new(substitute(lhs, bound)?),
            Box::new(substitute(rhs, bound)?),
        ),
        Expr::Call(target, args) => Expr::Call(
            target.clone(),
            args.iter()
                .map(|arg| substitute(arg, bound))
                .collect::<Option<Vec<_>>>()?,
        ),
        _ => return None,
    };
    Some(Spanned::new(node, expr.span))
}

/// What a guard over literals alone comes to, when it comes to anything: the
/// boolean literals, `not`, `and`, `or`, an integer comparison, and a call to
/// a helper that is only a type test.
fn decide<TypeHandle>(
    expr: &Expr,
    resolver: &mut impl PatternResolver<TypeHandle>,
) -> Result<Option<bool>, SourcePatternError> {
    Ok(match expr {
        Expr::Bool(value) => Some(*value),
        Expr::UnOp(UnOp::Not, arg) => decide(&arg.node, resolver)?.map(|value| !value),
        Expr::BinOp(BinOp::And, lhs, rhs) => {
            let (lhs, rhs) = (decide(&lhs.node, resolver)?, decide(&rhs.node, resolver)?);
            match (lhs, rhs) {
                (Some(false), _) | (_, Some(false)) => Some(false),
                (Some(true), Some(true)) => Some(true),
                _ => None,
            }
        }
        Expr::BinOp(BinOp::Or, lhs, rhs) => {
            let (lhs, rhs) = (decide(&lhs.node, resolver)?, decide(&rhs.node, resolver)?);
            match (lhs, rhs) {
                (Some(true), _) | (_, Some(true)) => Some(true),
                (Some(false), Some(false)) => Some(false),
                _ => None,
            }
        }
        Expr::BinOp(op, lhs, rhs) => match (&lhs.node, &rhs.node) {
            (Expr::Int(lhs), Expr::Int(rhs)) => compare(*op, lhs, rhs),
            _ => None,
        },
        Expr::Call(target, args) => decide_type_test(&target.node, args, resolver)?,
        _ => None,
    })
}

fn compare(op: BinOp, lhs: &i64, rhs: &i64) -> Option<bool> {
    Some(match op {
        BinOp::Eq => lhs == rhs,
        BinOp::Neq => lhs != rhs,
        BinOp::Lt => lhs < rhs,
        BinOp::LtEq => lhs <= rhs,
        BinOp::Gt => lhs > rhs,
        BinOp::GtEq => lhs >= rhs,
        _ => return None,
    })
}

/// A call to a type-test helper whose arguments are all literals: whether each
/// literal has the type its argument is asked.
fn decide_type_test<TypeHandle>(
    target: &Expr,
    args: &[Spanned<Expr>],
    resolver: &mut impl PatternResolver<TypeHandle>,
) -> Result<Option<bool>, SourcePatternError> {
    let Some(callee) = Callee::for_call(target, args.len()) else {
        return Ok(None);
    };
    let literals = args.iter().map(|arg| literal_of(&arg.node)).collect::<Option<Vec<_>>>();
    let Some(literals) = literals else {
        return Ok(None);
    };
    let Some(GuardCallee::Helper(helper)) = resolver.guard_call(&callee, args.len())? else {
        return Ok(None);
    };
    let Some(asked) = &helper.type_predicate else {
        return Ok(None);
    };
    let mut verdict = Some(true);
    for (argument, ty) in asked {
        match resolver.literal_has_type(&literals[*argument as usize], ty) {
            Some(true) => {}
            Some(false) => return Ok(Some(false)),
            None => verdict = None,
        }
    }
    Ok(verdict)
}
