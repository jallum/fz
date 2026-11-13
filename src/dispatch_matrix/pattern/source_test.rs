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

fn guard_extern(
    params: &[crate::fz_ir::ExternTy],
    ret: crate::fz_ir::ExternReturn,
    variadic: bool,
) -> Result<crate::dispatch_matrix::pattern::GuardExtern, SourcePatternError> {
    crate::dispatch_matrix::pattern::GuardExtern::new(crate::fz_ir::ExternAbi::C, "probe", params, ret, variadic)
}

#[test]
fn a_guard_extern_of_integers_and_reference_words_is_admitted() {
    use crate::fz_ir::{ExternReturn, ExternTy};
    let admitted = guard_extern(
        &[ExternTy::Any, ExternTy::I64],
        ExternReturn::Scalar(ExternTy::Any),
        false,
    )
    .expect("integer and reference-word classes are the two every guard evaluator carries");
    assert!(!admitted.fails_the_guard());
}

#[test]
fn a_guard_extern_returning_never_fails_the_guard() {
    use crate::fz_ir::{ExternReturn, ExternTy};
    let aborting = guard_extern(&[ExternTy::Any], ExternReturn::Scalar(ExternTy::Never), false)
        .expect("a call that aborts is how a guard function says its argument is outside its domain");
    assert!(aborting.fails_the_guard());
}

#[test]
fn a_guard_extern_of_any_other_class_is_refused_where_the_node_is_made() {
    use crate::fz_ir::{ExternReturn, ExternTy};
    let refused = [
        guard_extern(&[ExternTy::Binary], ExternReturn::Scalar(ExternTy::I64), false),
        guard_extern(&[ExternTy::Any], ExternReturn::Scalar(ExternTy::Unit), false),
        guard_extern(&[ExternTy::Any], ExternReturn::Scalar(ExternTy::I64), true),
    ];
    for result in refused {
        assert!(
            matches!(result, Err(SourcePatternError::GuardExternClass { .. })),
            "expected a class refusal, got {result:?}"
        );
    }
}

/// Intent: a guard function may answer a boolean, which is how a comparison
/// such as `===` is a guard, plainly or with a declared failure.
#[test]
fn a_guard_extern_may_return_a_boolean() {
    use crate::fz_ir::{ExternReturn, ExternTy};
    let admitted = guard_extern(
        &[ExternTy::Any, ExternTy::Any],
        ExternReturn::Scalar(ExternTy::Bool),
        false,
    );
    assert!(admitted.is_ok(), "expected the extern to be admitted, got {admitted:?}");
}

/// Intent: a guard function may take and return numbers, and may declare a
/// failure, because a guard calls the same Kernel operators a body does.
#[test]
fn a_guard_extern_may_carry_floats_and_declare_a_checked_failure() {
    use crate::dispatch_matrix::pattern::LastResort;
    use crate::fz_ir::{ExternReturn, ExternTy};
    let overflow = || LastResort::Exception {
        exception: "Elixir.ArithmeticError".into(),
        message: "bad argument in arithmetic expression".to_string(),
        shows_subject: false,
    };
    let admitted = [
        guard_extern(
            &[ExternTy::F64, ExternTy::F64],
            ExternReturn::Scalar(ExternTy::F64),
            false,
        ),
        guard_extern(
            &[ExternTy::I64, ExternTy::I64],
            ExternReturn::Checked(ExternTy::I64, overflow()),
            false,
        ),
        guard_extern(
            &[ExternTy::I64, ExternTy::I64],
            ExternReturn::Checked(ExternTy::F64, overflow()),
            false,
        ),
    ];
    for result in admitted {
        assert!(result.is_ok(), "expected the extern to be admitted, got {result:?}");
    }
}

fn both(left: Pattern, right: Pattern) -> Pattern {
    Pattern::Both(Box::new(sp(left)), Box::new(sp(right)))
}

/// Intent: `{a, _} = {_, b}` binds the names of both sides, so a name on
/// either side is visible to the clause body.
#[test]
fn both_sides_of_an_equals_pattern_contribute_bound_names() {
    let pattern = both(
        Pattern::Tuple(vec![sp(Pattern::Var(Var::user("a"))), sp(Pattern::Wildcard)]),
        Pattern::Tuple(vec![sp(Pattern::Wildcard), sp(Pattern::Var(Var::user("b")))]),
    );
    let mut names = BTreeSet::new();
    collect_bound_names_in_pattern(&pattern, &mut names);

    assert_eq!(names, BTreeSet::from([Var::user("a"), Var::user("b")]));
}

/// Intent: a pin on either side of `=` is a requirement of the clause.
#[test]
fn a_pin_on_either_side_of_an_equals_pattern_is_collected() {
    let pattern = both(Pattern::Pinned(Var::user("p")), Pattern::Pinned(Var::user("q")));
    let mut pins = Vec::new();
    collect_pinned_names_in_pattern(&sp(pattern), &mut pins);

    let names: Vec<_> = pins.iter().map(|pin| pin.name.name.clone()).collect();
    assert_eq!(names, vec!["p", "q"]);
}

/// Intent: asking the same shape question twice of one subject compiles, and
/// the row it guards is still reached.
#[test]
fn the_same_question_twice_on_one_subject_compiles_to_one_reachable_row() {
    let pair = || Pattern::Tuple(vec![sp(Pattern::Wildcard), sp(Pattern::Wildcard)]);
    let patterns = SourcePatternRows::lexical(
        1,
        vec![row(vec![both(pair(), pair())], 0), row(vec![Pattern::Wildcard], 1)],
    );

    assert!(redundant_rows(&patterns).is_empty());
}
