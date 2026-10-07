use super::*;
use crate::ast::{Expr, Pattern, Spanned};
use crate::compiler2::{Ty, Types};
use crate::dispatch_matrix::pattern::{PatternDispatchError, PatternSubjectRef, pattern_dispatch_from_source};

fn sp<T>(node: T) -> Spanned<T> {
    Spanned::dummy(node)
}

fn row(patterns: Vec<Pattern>, body_id: PatternBodyId) -> PatternRow<Ty> {
    PatternRow {
        patterns: patterns.into_iter().map(sp).collect(),
        preconditions: Vec::new(),
        guard: None,
        body_id,
    }
}

fn row_with_guard(patterns: Vec<Pattern>, body_id: PatternBodyId) -> PatternRow<Ty> {
    row_with_guard_expr(patterns, body_id, Expr::Bool(true))
}

fn row_with_guard_expr(patterns: Vec<Pattern>, body_id: PatternBodyId, guard: Expr) -> PatternRow<Ty> {
    PatternRow {
        patterns: patterns.into_iter().map(sp).collect(),
        preconditions: Vec::new(),
        guard: Some(sp(guard)),
        body_id,
    }
}

/// Test-only convenience: compiles `patterns` with a resolver that answers no
/// guard call, then reports its redundant rows. Production callers always
/// pass their own already-compiled plan and their own real resolver.
fn redundant_rows(patterns: &SourcePatternRows<Ty>) -> Vec<RedundantRow> {
    let mut resolver = |_callee: &crate::ast::Callee, _arity: usize| Ok(None);
    let plan = pattern_dispatch_from_source(patterns.clone()).expect("test patterns must compile");
    find_redundant_rows_with_resolver(patterns, &plan, &mut resolver)
}

fn redundant_body_ids(patterns: &SourcePatternRows<Ty>) -> Vec<PatternBodyId> {
    redundant_rows(patterns).into_iter().map(|row| row.body_id).collect()
}

#[test]
fn source_pattern_rows_reject_non_monotonic_body_ids() {
    let patterns = SourcePatternRows::lexical(
        1,
        vec![row(vec![Pattern::Wildcard], 2), row(vec![Pattern::Wildcard], 1)],
    );

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
    let patterns = SourcePatternRows::lexical(1, vec![row(vec![Pattern::Wildcard], 0), row(vec![Pattern::Int(42)], 1)]);

    let redundant = redundant_rows(&patterns);
    assert_eq!(
        redundant,
        vec![RedundantRow {
            body_id: 1,
            always_matches: 0
        }]
    );
}

#[test]
fn duplicate_literal_rows_are_unreachable() {
    let floats = SourcePatternRows::lexical(
        1,
        vec![row(vec![Pattern::Float(1.5)], 0), row(vec![Pattern::Float(1.5)], 1)],
    );
    let binaries = SourcePatternRows::lexical(
        1,
        vec![
            row(vec![Pattern::Binary(b"hi".to_vec())], 0),
            row(vec![Pattern::Binary(b"hi".to_vec())], 1),
        ],
    );

    assert_eq!(redundant_body_ids(&floats), vec![1]);
    assert_eq!(redundant_body_ids(&binaries), vec![1]);
}

#[test]
fn guarded_row_does_not_dominate_later_row() {
    let patterns = SourcePatternRows::lexical(
        1,
        vec![
            row_with_guard(vec![Pattern::Wildcard], 0),
            row(vec![Pattern::Wildcard], 1),
        ],
    );

    assert!(redundant_rows(&patterns).is_empty());
}

#[test]
fn unguarded_wildcard_still_dominates_after_guarded_row() {
    let patterns = SourcePatternRows::lexical(
        1,
        vec![
            row_with_guard(vec![Pattern::Wildcard], 0),
            row(vec![Pattern::Wildcard], 1),
            row(vec![Pattern::Int(42)], 2),
        ],
    );

    assert_eq!(redundant_body_ids(&patterns), vec![2]);
    assert_eq!(redundant_rows(&patterns)[0].always_matches, 1);
}

#[test]
fn guarded_row_unreachable_under_unguarded_cover() {
    let patterns = SourcePatternRows::lexical(
        1,
        vec![
            row(vec![Pattern::Wildcard], 0),
            row_with_guard(vec![Pattern::Wildcard], 1),
        ],
    );

    assert_eq!(
        redundant_rows(&patterns),
        vec![RedundantRow {
            body_id: 1,
            always_matches: 0
        }]
    );
}

#[test]
fn source_pattern_rows_reject_row_arity_mismatch() {
    let patterns = SourcePatternRows::lexical(1, vec![row(vec![Pattern::Wildcard, Pattern::Wildcard], 0)]);

    let err = pattern_dispatch_from_source(patterns).expect_err("row arity must match input count");
    assert!(matches!(
        err,
        PatternDispatchError::SourcePattern(SourcePatternError::RowPatternArity {
            expected: 1,
            actual: 2,
            body_id: 0,
        })
    ));
}

#[test]
fn source_pattern_rows_reject_unknown_input_precondition() {
    let mut types = Types::new();
    let patterns = SourcePatternRows::lexical(
        1,
        vec![PatternRow {
            patterns: vec![sp(Pattern::Wildcard)],
            preconditions: vec![(PatternSubjectRef::Input(1), types.int())],
            guard: None,
            body_id: 0,
        }],
    );

    let err = pattern_dispatch_from_source(patterns).expect_err("precondition inputs must exist");
    assert!(matches!(
        err,
        PatternDispatchError::SourcePattern(SourcePatternError::UnknownSubject(PatternSubjectRef::Input(1)))
    ));
}
