// ---------------------------------------------------------------------------
// fz-ul4.45 — Exhaustiveness + unreachability analysis
// ---------------------------------------------------------------------------

use std::collections::BTreeSet;

use crate::ast::{Expr, Spanned};
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, pattern_dispatch_from_matrix};
use crate::dispatch_matrix::{DispatchNode, GraphNodeId, ListRegion, Region, SubjectId};

use super::{BodyId, PatternMatrix, SubjectDomain};

/// Body ids that no path through the matcher graph reaches. Guarded rows do
/// not consume coverage: for diagnostics we replace concrete guards with
/// `true`, compile one matcher, and traverse both guard branches. That keeps
/// the "guard may reject" fallthrough edge without evaluating guard bodies.
pub fn find_unreachable_rows(pattern_matrix: &PatternMatrix) -> Vec<BodyId> {
    let row_bodies: BTreeSet<BodyId> = pattern_matrix.rows.iter().map(|r| r.body_id).collect();
    let plan = plan_for_analysis(normalize_guards_for_analysis(pattern_matrix.clone()));
    let mut reached = BTreeSet::new();
    collect_reachable_bodies_from_graph(&plan, plan.graph.root, &mut reached);
    row_bodies.difference(&reached).copied().collect()
}

/// True if any path through the matcher graph leads to Fail — i.e., the
/// PatternMatrix doesn't cover all possible subject values. Lowerers like
/// lower_case translate this to a runtime `:case_clause` halt; the warning
/// surfaces the gap at compile time.
#[cfg(test)]
pub fn is_inexhaustive(pattern_matrix: &PatternMatrix) -> bool {
    is_inexhaustive_with_domains(pattern_matrix, &[])
}

pub fn is_inexhaustive_with_domains(pattern_matrix: &PatternMatrix, domains: &[SubjectDomain]) -> bool {
    let normalized = normalize_guards_for_analysis(pattern_matrix.clone());
    let plan = plan_for_analysis(normalized);
    has_reachable_fail_in_graph(&plan, plan.graph.root)
        && !list_domain_is_covered_in_dispatch_matrix(pattern_matrix, domains, &plan)
}

fn plan_for_analysis(pattern_matrix: PatternMatrix) -> PatternDispatchPlan {
    pattern_dispatch_from_matrix(pattern_matrix).expect("pattern analysis dispatch matrix must compile")
}

fn normalize_guards_for_analysis(mut pattern_matrix: PatternMatrix) -> PatternMatrix {
    for row in &mut pattern_matrix.rows {
        if row.guard.is_some() {
            row.guard = Some(Spanned::dummy(Expr::Bool(true)));
        }
    }
    pattern_matrix
}

fn collect_reachable_bodies_from_graph(plan: &PatternDispatchPlan, node: GraphNodeId, out: &mut BTreeSet<BodyId>) {
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

fn list_domain_is_covered_in_dispatch_matrix(
    pattern_matrix: &PatternMatrix,
    domains: &[SubjectDomain],
    plan: &PatternDispatchPlan,
) -> bool {
    if domains.is_empty() {
        return false;
    }
    if pattern_matrix
        .rows
        .iter()
        .any(|row| row.guard.is_some() || !row.preconditions.is_empty())
    {
        return false;
    }
    domains
        .iter()
        .enumerate()
        .filter(|(_, domain)| **domain == SubjectDomain::List)
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
