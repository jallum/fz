// ---------------------------------------------------------------------------
// fz-ul4.45 — Exhaustiveness + unreachability analysis
// ---------------------------------------------------------------------------

use std::collections::{BTreeSet, HashMap};

use crate::ast::{Expr, Spanned};
use crate::exec::matcher::{Matcher, MatcherNode, NodeId, SubjectRef, SwitchKey, SwitchKind};
use crate::fz_ir::Var;

use super::{BodyId, PatternMatrix, SubjectDomain, compile_pattern_matrix};

/// Body ids that no path through the matcher graph reaches. Guarded rows do
/// not consume coverage: for diagnostics we replace concrete guards with
/// `true`, compile one matcher, and traverse both guard branches. That keeps
/// the "guard may reject" fallthrough edge without evaluating guard bodies.
pub fn find_unreachable_rows(pattern_matrix: &PatternMatrix) -> Vec<BodyId> {
    let row_bodies: BTreeSet<BodyId> = pattern_matrix.rows.iter().map(|r| r.body_id).collect();
    let matcher = matcher_for_analysis(normalize_guards_for_analysis(pattern_matrix.clone()));
    let mut reached = BTreeSet::new();
    collect_reachable_bodies_from_matcher(&matcher, matcher.root, &mut reached);
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
    let matcher = matcher_for_analysis(normalize_guards_for_analysis(pattern_matrix.clone()));
    let domain_by_subject: HashMap<Var, SubjectDomain> = pattern_matrix
        .subjects
        .iter()
        .copied()
        .zip(domains.iter().copied())
        .collect();
    has_reachable_fail_in_matcher(&matcher, matcher.root, &domain_by_subject)
}

fn matcher_for_analysis(pattern_matrix: PatternMatrix) -> Matcher {
    compile_pattern_matrix(pattern_matrix).expect("pattern analysis matcher must compile")
}

fn normalize_guards_for_analysis(mut pattern_matrix: PatternMatrix) -> PatternMatrix {
    for row in &mut pattern_matrix.rows {
        if row.guard.is_some() {
            row.guard = Some(Spanned::dummy(Expr::Bool(true)));
        }
    }
    pattern_matrix
}

fn collect_reachable_bodies_from_matcher(matcher: &Matcher, node: NodeId, out: &mut BTreeSet<BodyId>) {
    let Some(node) = matcher.node(node) else {
        return;
    };
    match node {
        MatcherNode::Fail { .. } => {}
        MatcherNode::Leaf(leaf) => {
            out.insert(leaf.body_id);
        }
        MatcherNode::Switch { cases, default, .. } => {
            for (_, sub) in cases {
                collect_reachable_bodies_from_matcher(matcher, *sub, out);
            }
            collect_reachable_bodies_from_matcher(matcher, *default, out);
        }
        MatcherNode::Test { on_true, on_false, .. } | MatcherNode::Guard { on_true, on_false, .. } => {
            collect_reachable_bodies_from_matcher(matcher, *on_true, out);
            collect_reachable_bodies_from_matcher(matcher, *on_false, out);
        }
    }
}

fn has_reachable_fail_in_matcher(
    matcher: &Matcher,
    node: NodeId,
    domain_by_subject: &HashMap<Var, SubjectDomain>,
) -> bool {
    let Some(node_ref) = matcher.node(node) else {
        return false;
    };
    match node_ref {
        MatcherNode::Fail { .. } => true,
        MatcherNode::Leaf(_) => false,
        MatcherNode::Switch { cases, default, .. } => {
            if cases
                .iter()
                .any(|(_, sub)| has_reachable_fail_in_matcher(matcher, *sub, domain_by_subject))
            {
                return true;
            }
            if list_domain_is_covered_in_matcher(matcher, node, domain_by_subject) {
                return false;
            }
            has_reachable_fail_in_matcher(matcher, *default, domain_by_subject)
        }
        MatcherNode::Test { on_true, on_false, .. } | MatcherNode::Guard { on_true, on_false, .. } => {
            has_reachable_fail_in_matcher(matcher, *on_true, domain_by_subject)
                || has_reachable_fail_in_matcher(matcher, *on_false, domain_by_subject)
        }
    }
}

fn list_domain_is_covered_in_matcher(
    matcher: &Matcher,
    node: NodeId,
    domain_by_subject: &HashMap<Var, SubjectDomain>,
) -> bool {
    let Some(MatcherNode::Switch {
        subject,
        kind: SwitchKind::ListCons,
        cases,
        ..
    }) = matcher.node(node)
    else {
        return false;
    };
    if matcher_subject_root_var(matcher, subject).and_then(|v| domain_by_subject.get(&v).copied())
        != Some(SubjectDomain::List)
    {
        return false;
    }
    let has_empty = cases.iter().any(|(key, _)| matches!(key, SwitchKey::EmptyList));
    let has_cons = cases.iter().any(|(key, _)| matches!(key, SwitchKey::Cons));
    has_empty && has_cons
}

fn matcher_subject_root_var(matcher: &Matcher, subject: &SubjectRef) -> Option<Var> {
    let input = match subject {
        SubjectRef::Input(input) => *input,
        SubjectRef::TupleField { tuple, .. }
        | SubjectRef::ListHead(tuple)
        | SubjectRef::ListTail(tuple)
        | SubjectRef::MapValue { map: tuple, .. }
        | SubjectRef::BitstringField { bitstring: tuple, .. } => return matcher_subject_root_var(matcher, tuple),
    };
    matcher.inputs.get(input.0 as usize).and_then(|i| i.var)
}
