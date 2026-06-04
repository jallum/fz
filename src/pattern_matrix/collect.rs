use std::collections::{BTreeSet, HashMap};

use crate::ast::{Expr, Pattern, Spanned};
use crate::exec::matcher::{InputId, MatcherBinding, PinnedId};

use super::pattern_ops::append_pattern_ops;
use super::{PatternMatrix, PatternMatrixCompileError, SubjectRef};

pub fn collect_matcher_pattern_bindings(
    patterns: &[Spanned<Pattern>],
    pinned_by_name: &HashMap<String, PinnedId>,
) -> Result<Vec<MatcherBinding>, PatternMatrixCompileError> {
    let mut tests = Vec::new();
    let mut bindings = Vec::new();
    let mut prepared_keys = Vec::new();
    for (index, pattern) in patterns.iter().enumerate() {
        append_pattern_ops(
            &pattern.node,
            crate::exec::matcher::SubjectRef::Input(InputId(index as u32)),
            pinned_by_name,
            &mut prepared_keys,
            &mut tests,
            &mut bindings,
        )?;
    }
    Ok(bindings)
}

pub(crate) fn collect_pinned_names(pattern_matrix: &PatternMatrix) -> Vec<String> {
    let mut out = Vec::new();
    for row in &pattern_matrix.rows {
        let mut bound = BTreeSet::new();
        for pattern in &row.patterns {
            collect_pinned_names_in_pattern(&pattern.node, &mut out);
            collect_bound_names_in_pattern(&pattern.node, &mut bound);
        }
        if let Some(guard) = &row.guard {
            collect_guard_capture_names(&guard.node, &bound, &mut out);
        }
    }
    out
}

pub(crate) fn collect_bound_names_in_pattern(pattern: &Pattern, out: &mut BTreeSet<String>) {
    match pattern {
        Pattern::Var(name) | Pattern::As(name, _) => {
            out.insert(name.clone());
            if let Pattern::As(_, inner) = pattern {
                collect_bound_names_in_pattern(&inner.node, out);
            }
        }
        Pattern::Tuple(elems) | Pattern::List(elems, _) => {
            for elem in elems {
                collect_bound_names_in_pattern(&elem.node, out);
            }
            if let Pattern::List(_, Some(tail)) = pattern {
                collect_bound_names_in_pattern(&tail.node, out);
            }
        }
        Pattern::Map(entries) => {
            for (key, val) in entries {
                collect_bound_names_in_pattern(&key.node, out);
                collect_bound_names_in_pattern(&val.node, out);
            }
        }
        Pattern::Struct { fields, .. } => {
            for (_, val) in fields {
                collect_bound_names_in_pattern(&val.node, out);
            }
        }
        Pattern::Bitstring(fields) => {
            for field in fields {
                collect_bound_names_in_pattern(&field.value.node, out);
            }
        }
        Pattern::Wildcard
        | Pattern::Pinned(_)
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Binary(_)
        | Pattern::Atom(_)
        | Pattern::Bool(_)
        | Pattern::Nil => {}
    }
}

pub(crate) fn collect_guard_capture_names(expr: &Expr, bound: &BTreeSet<String>, out: &mut Vec<String>) {
    use crate::ast::Expr;
    match expr {
        Expr::Var(name) if !bound.contains(name) && !out.contains(name) => out.push(name.clone()),
        Expr::BinOp(_, a, b) => {
            collect_guard_capture_names(&a.node, bound, out);
            collect_guard_capture_names(&b.node, bound, out);
        }
        Expr::UnOp(_, a) | Expr::Ascribe(a, _) => collect_guard_capture_names(&a.node, bound, out),
        Expr::Call(target, args) => {
            if !matches!(&target.node, Expr::Var(_) | Expr::FnRef { .. }) {
                collect_guard_capture_names(&target.node, bound, out);
            }
            for arg in args {
                collect_guard_capture_names(&arg.node, bound, out);
            }
        }
        _ => {}
    }
}

pub(crate) fn collect_pinned_names_in_pattern(pattern: &Pattern, out: &mut Vec<String>) {
    match pattern {
        Pattern::Pinned(name) => {
            if !out.contains(name) {
                out.push(name.clone());
            }
        }
        Pattern::Tuple(elems) | Pattern::List(elems, _) => {
            for elem in elems {
                collect_pinned_names_in_pattern(&elem.node, out);
            }
            if let Pattern::List(_, Some(tail)) = pattern {
                collect_pinned_names_in_pattern(&tail.node, out);
            }
        }
        Pattern::Map(entries) => {
            for (key, val) in entries {
                collect_pinned_names_in_pattern(&key.node, out);
                collect_pinned_names_in_pattern(&val.node, out);
            }
        }
        Pattern::Struct { fields, .. } => {
            for (_, val) in fields {
                collect_pinned_names_in_pattern(&val.node, out);
            }
        }
        Pattern::As(_, inner) => collect_pinned_names_in_pattern(&inner.node, out),
        Pattern::Bitstring(fields) => {
            for field in fields {
                collect_pinned_names_in_pattern(&field.value.node, out);
            }
        }
        Pattern::Wildcard
        | Pattern::Var(_)
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Binary(_)
        | Pattern::Atom(_)
        | Pattern::Bool(_)
        | Pattern::Nil => {}
    }
}

pub(crate) fn collect_var_bindings(
    patterns: &[Spanned<Pattern>],
    subjects: &[SubjectRef],
) -> Vec<(String, SubjectRef)> {
    let mut out = Vec::new();
    for (p, subj) in patterns.iter().zip(subjects.iter()) {
        collect_one(&p.node, subj, &mut out);
    }
    out
}

pub(crate) fn collect_one(p: &Pattern, subj: &SubjectRef, out: &mut Vec<(String, SubjectRef)>) {
    match p {
        Pattern::Var(name) => out.push((name.clone(), subj.clone())),
        Pattern::As(name, inner) => {
            out.push((name.clone(), subj.clone()));
            collect_one(&inner.node, subj, out);
        }
        _ => {}
    }
}
