use super::*;
use crate::ast::{Expr, Pattern, Spanned};
use crate::dispatch_matrix::pattern::{PatternDispatchError, pattern_dispatch_from_source};
use crate::fz_ir::Var;

fn sp<T>(node: T) -> Spanned<T> {
    Spanned::dummy(node)
}

fn row(patterns: Vec<Pattern>, body_id: PatternBodyId) -> PatternRow {
    PatternRow {
        patterns: patterns.into_iter().map(sp).collect(),
        preconditions: Vec::new(),
        guard: None,
        body_id,
    }
}

fn row_with_guard(patterns: Vec<Pattern>, body_id: PatternBodyId) -> PatternRow {
    row_with_guard_expr(patterns, body_id, Expr::Bool(true))
}

fn row_with_guard_expr(patterns: Vec<Pattern>, body_id: PatternBodyId, guard: Expr) -> PatternRow {
    PatternRow {
        patterns: patterns.into_iter().map(sp).collect(),
        preconditions: Vec::new(),
        guard: Some(sp(guard)),
        body_id,
    }
}

#[test]
fn source_pattern_rows_reject_non_monotonic_body_ids() {
    let patterns = SourcePatternRows {
        subjects: vec![Var(0)],
        rows: vec![row(vec![Pattern::Wildcard], 2), row(vec![Pattern::Wildcard], 1)],
    };

    let err = pattern_dispatch_from_source(patterns).expect_err("source order must be monotonic");
    assert!(matches!(
        err,
        PatternDispatchError::SourcePattern(SourcePatternError::NonMonotonicBodyId {
            previous: 2,
            current: 1,
        })
    ));
}

#[test]
fn unreachable_row_after_wildcard_detected() {
    let patterns = SourcePatternRows {
        subjects: vec![Var(0)],
        rows: vec![row(vec![Pattern::Wildcard], 0), row(vec![Pattern::Int(42)], 1)],
    };

    assert_eq!(find_unreachable_rows(&patterns), vec![1]);
}

#[test]
fn duplicate_literal_rows_are_unreachable() {
    let floats = SourcePatternRows {
        subjects: vec![Var(0)],
        rows: vec![row(vec![Pattern::Float(1.5)], 0), row(vec![Pattern::Float(1.5)], 1)],
    };
    let binaries = SourcePatternRows {
        subjects: vec![Var(0)],
        rows: vec![
            row(vec![Pattern::Binary(b"hi".to_vec())], 0),
            row(vec![Pattern::Binary(b"hi".to_vec())], 1),
        ],
    };

    assert_eq!(find_unreachable_rows(&floats), vec![1]);
    assert_eq!(find_unreachable_rows(&binaries), vec![1]);
}

#[test]
fn guarded_row_does_not_dominate_later_row() {
    let patterns = SourcePatternRows {
        subjects: vec![Var(0)],
        rows: vec![
            row_with_guard(vec![Pattern::Wildcard], 0),
            row(vec![Pattern::Wildcard], 1),
        ],
    };

    assert!(find_unreachable_rows(&patterns).is_empty());
}

#[test]
fn guarded_reachability_does_not_lower_guard_expression() {
    let unsupported_guard = Expr::Call(Box::new(sp(Expr::Var("opaque".to_string()))), vec![]);
    let reachable = SourcePatternRows {
        subjects: vec![Var(0)],
        rows: vec![
            row_with_guard_expr(vec![Pattern::Wildcard], 0, unsupported_guard),
            row(vec![Pattern::Wildcard], 1),
        ],
    };
    assert!(find_unreachable_rows(&reachable).is_empty());

    let inexhaustive = SourcePatternRows {
        subjects: vec![Var(0)],
        rows: vec![row_with_guard_expr(
            vec![Pattern::Wildcard],
            0,
            Expr::Call(Box::new(sp(Expr::Var("opaque".to_string()))), vec![]),
        )],
    };
    assert!(is_inexhaustive(&inexhaustive));
}

#[test]
fn unguarded_wildcard_still_dominates_after_guarded_row() {
    let patterns = SourcePatternRows {
        subjects: vec![Var(0)],
        rows: vec![
            row_with_guard(vec![Pattern::Wildcard], 0),
            row(vec![Pattern::Wildcard], 1),
            row(vec![Pattern::Int(42)], 2),
        ],
    };

    assert_eq!(find_unreachable_rows(&patterns), vec![2]);
}

#[test]
fn guarded_row_unreachable_under_unguarded_cover() {
    let patterns = SourcePatternRows {
        subjects: vec![Var(0)],
        rows: vec![
            row(vec![Pattern::Wildcard], 0),
            row_with_guard(vec![Pattern::Wildcard], 1),
        ],
    };

    assert_eq!(find_unreachable_rows(&patterns), vec![1]);
}

#[test]
fn exhaustiveness_tracks_dispatch_graph_fallthrough() {
    let missing_wildcard = SourcePatternRows {
        subjects: vec![Var(0)],
        rows: vec![row(vec![Pattern::Int(0)], 0), row(vec![Pattern::Int(1)], 1)],
    };
    let covered = SourcePatternRows {
        subjects: vec![Var(0)],
        rows: vec![row(vec![Pattern::Int(0)], 0), row(vec![Pattern::Wildcard], 1)],
    };

    assert!(is_inexhaustive(&missing_wildcard));
    assert!(!is_inexhaustive(&covered));
}

#[test]
fn empty_list_and_cons_exhaust_list_domain_only() {
    let cons = Pattern::List(
        vec![sp(Pattern::Var("h".to_string()))],
        Some(Box::new(sp(Pattern::Var("t".to_string())))),
    );
    let patterns = SourcePatternRows {
        subjects: vec![Var(0)],
        rows: vec![row(vec![Pattern::List(vec![], None)], 0), row(vec![cons], 1)],
    };

    assert!(!is_inexhaustive_with_domains(&patterns, &[KnownSubjectDomain::List]));
    assert!(is_inexhaustive_with_domains(&patterns, &[KnownSubjectDomain::Any]));
}
