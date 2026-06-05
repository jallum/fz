use std::collections::BTreeSet;

use crate::ast::{Expr, Pattern, Spanned};
use crate::dispatch_matrix::{DispatchNode, GraphNodeId, ListRegion, Region, SubjectId};
use crate::fz_ir::Var;
use crate::types::Ty;

use super::{PatternDispatchPlan, pattern_dispatch_from_source};

/// Opaque handle into the caller's body table. Source-pattern dispatch never
/// lowers bodies; it routes graph outcomes to caller-owned body lowering by id.
pub(crate) type PatternBodyId = u32;

#[derive(Debug, Clone)]
pub(crate) struct PatternRow {
    /// Column patterns. `patterns.len()` must equal `SourcePatternRows::subjects.len()`.
    pub(crate) patterns: Vec<Spanned<Pattern>>,
    /// `@spec` annotation tests evaluated at leaf-resolution time, before the guard.
    pub(crate) preconditions: Vec<(Var, Ty)>,
    pub(crate) guard: Option<Spanned<Expr>>,
    pub(crate) body_id: PatternBodyId,
}

#[derive(Debug, Clone)]
pub(crate) struct SourcePatternRows {
    pub(crate) subjects: Vec<Var>,
    pub(crate) rows: Vec<PatternRow>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum KnownSubjectDomain {
    Any,
    List,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SourcePatternError {
    UnsupportedGuardExpr,
    UnsupportedMapKey,
    UnknownSubject(Var),
    UnknownPinned(String),
    UnknownGuardVar(String),
    GuardCallCycle(String, usize),
    DispatchMatrix(String),
    NonMonotonicBodyId {
        previous: PatternBodyId,
        current: PatternBodyId,
    },
}

pub(crate) fn collect_pinned_names(patterns: &SourcePatternRows) -> Vec<String> {
    let mut out = Vec::new();
    for row in &patterns.rows {
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

fn collect_pinned_names_in_pattern(pattern: &Pattern, out: &mut Vec<String>) {
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

pub(crate) fn direct_bitfield_bindings(pattern: &Pattern) -> Vec<String> {
    match pattern {
        Pattern::Var(name) => vec![name.clone()],
        Pattern::As(name, inner) => {
            let mut out = vec![name.clone()];
            out.extend(direct_bitfield_bindings(&inner.node));
            out
        }
        _ => Vec::new(),
    }
}

/// Body ids that no path through the dispatch graph reaches. Guarded rows do
/// not consume coverage: for diagnostics we replace concrete guards with
/// `true`, compile one dispatch plan, and traverse both guard branches.
pub(crate) fn find_unreachable_rows(patterns: &SourcePatternRows) -> Vec<PatternBodyId> {
    let row_bodies: BTreeSet<PatternBodyId> = patterns.rows.iter().map(|r| r.body_id).collect();
    let plan = plan_for_analysis(normalize_guards_for_analysis(patterns.clone()));
    let mut reached = BTreeSet::new();
    collect_reachable_bodies_from_graph(&plan, plan.graph.root, &mut reached);
    row_bodies.difference(&reached).copied().collect()
}

#[cfg(test)]
pub(crate) fn is_inexhaustive(patterns: &SourcePatternRows) -> bool {
    is_inexhaustive_with_domains(patterns, &[])
}

pub(crate) fn is_inexhaustive_with_domains(patterns: &SourcePatternRows, domains: &[KnownSubjectDomain]) -> bool {
    let normalized = normalize_guards_for_analysis(patterns.clone());
    let plan = plan_for_analysis(normalized);
    has_reachable_fail_in_graph(&plan, plan.graph.root) && !list_domain_is_covered(patterns, domains, &plan)
}

fn plan_for_analysis(patterns: SourcePatternRows) -> PatternDispatchPlan {
    pattern_dispatch_from_source(patterns).expect("source-pattern dispatch analysis must compile")
}

fn normalize_guards_for_analysis(mut patterns: SourcePatternRows) -> SourcePatternRows {
    for row in &mut patterns.rows {
        if row.guard.is_some() {
            row.guard = Some(Spanned::dummy(Expr::Bool(true)));
        }
    }
    patterns
}

fn collect_reachable_bodies_from_graph(
    plan: &PatternDispatchPlan,
    node: GraphNodeId,
    out: &mut BTreeSet<PatternBodyId>,
) {
    let Some(node) = plan.graph.node(node) else {
        return;
    };
    match node {
        DispatchNode::Fail => {}
        DispatchNode::Outcome { outcome, .. } => {
            if let Some(outcome) = plan.outcomes.iter().find(|entry| entry.outcome == *outcome) {
                out.insert(outcome.body_id);
            }
        }
        DispatchNode::Test { on_match, on_miss, .. } => {
            collect_reachable_bodies_from_graph(plan, on_match.target, out);
            collect_reachable_bodies_from_graph(plan, on_miss.target, out);
        }
    }
}

fn has_reachable_fail_in_graph(plan: &PatternDispatchPlan, node: GraphNodeId) -> bool {
    let Some(node_ref) = plan.graph.node(node) else {
        return false;
    };
    match node_ref {
        DispatchNode::Fail => true,
        DispatchNode::Outcome { .. } => false,
        DispatchNode::Test { on_match, on_miss, .. } => {
            has_reachable_fail_in_graph(plan, on_match.target) || has_reachable_fail_in_graph(plan, on_miss.target)
        }
    }
}

fn list_domain_is_covered(
    patterns: &SourcePatternRows,
    domains: &[KnownSubjectDomain],
    plan: &PatternDispatchPlan,
) -> bool {
    if domains.is_empty() {
        return false;
    }
    if patterns
        .rows
        .iter()
        .any(|row| row.guard.is_some() || !row.preconditions.is_empty())
    {
        return false;
    }
    domains
        .iter()
        .enumerate()
        .filter(|(_, domain)| **domain == KnownSubjectDomain::List)
        .any(|(index, _)| {
            let subject = SubjectId(index as u32);
            let only_simple_list_partition = plan.matrix.arms.iter().all(|arm| {
                arm.questions.len() == 1
                    && arm.questions.iter().all(|question| {
                        question.predicate.subject == subject
                            && matches!(
                                question.predicate.region,
                                Region::List(ListRegion::Empty) | Region::List(ListRegion::Cons)
                            )
                    })
            });
            if !only_simple_list_partition {
                return false;
            }
            let has_empty = plan.matrix.arms.iter().any(|arm| {
                arm.questions.iter().any(|question| {
                    question.predicate.subject == subject
                        && matches!(question.predicate.region, Region::List(ListRegion::Empty))
                })
            });
            let has_cons = plan.matrix.arms.iter().any(|arm| {
                arm.questions.iter().any(|question| {
                    question.predicate.subject == subject
                        && matches!(question.predicate.region, Region::List(ListRegion::Cons))
                })
            });
            has_empty && has_cons
        })
}

#[cfg(test)]
#[path = "source_test.rs"]
mod source_test;
