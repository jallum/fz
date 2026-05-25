use super::*;
use crate::ast::{Pattern, Spanned};
use crate::diag::FileId;

fn sp<T>(node: T) -> Spanned<T> {
    let _ = FileId(0);
    Spanned::dummy(node)
}

fn row(patterns: Vec<Pattern>, body_id: BodyId) -> Row {
    Row {
        patterns: patterns.into_iter().map(sp).collect(),
        preconditions: Vec::new(),
        bindings: Vec::new(),
        guard: None,
        body_id,
    }
}

#[test]
fn pattern_matrix_rejects_non_monotonic_body_ids() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row(vec![Pattern::Wildcard], 2),
            row(vec![Pattern::Wildcard], 1),
        ],
    };

    assert_eq!(
        compile_pattern_matrix(pattern_matrix),
        Err(PatternMatrixCompileError::NonMonotonicBodyId {
            previous: 2,
            current: 1,
        })
    );
}

// ── fz-ul4.45 — exhaustiveness + unreachability ─────────────────────

#[test]
fn unreachable_row_after_wildcard_detected() {
    // Row 0 wildcard catches everything; row 1 unreachable.
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row(vec![Pattern::Wildcard], 0),
            row(vec![Pattern::Int(42)], 1),
        ],
    };
    let dead = find_unreachable_rows(&pattern_matrix);
    assert_eq!(dead, vec![1]);
}

#[test]
fn unreachable_row_after_full_atom_cover() {
    // Two atoms exhaust... no, atom space is infinite via wildcard.
    // Just check: row 0 matches :a, row 1 is :a too (unreachable).
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row(vec![Pattern::Atom("a".to_string())], 0),
            row(vec![Pattern::Atom("a".to_string())], 1),
        ],
    };
    let dead = find_unreachable_rows(&pattern_matrix);
    assert_eq!(dead, vec![1]);
}

fn row_with_guard(patterns: Vec<Pattern>, body_id: BodyId) -> Row {
    row_with_guard_expr(patterns, body_id, crate::ast::Expr::Bool(true))
}

fn row_with_guard_expr(patterns: Vec<Pattern>, body_id: BodyId, guard: Expr) -> Row {
    Row {
        patterns: patterns.into_iter().map(sp).collect(),
        preconditions: Vec::new(),
        bindings: Vec::new(),
        // Analysis cares that a guard can reject; it must not depend on
        // whether the concrete guard expression is executable by Matcher.
        guard: Some(sp(guard)),
        body_id,
    }
}

/// fz-rcp.2 — a guarded row does NOT consume coverage. The row
/// that follows it with the same pattern is reachable (the guard
/// can reject at runtime).
#[test]
fn guarded_row_does_not_dominate_later_row() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row_with_guard(vec![Pattern::Wildcard], 0),
            row(vec![Pattern::Wildcard], 1),
        ],
    };
    let dead = find_unreachable_rows(&pattern_matrix);
    assert!(
        dead.is_empty(),
        "guarded row should not mark unguarded successor unreachable, got {:?}",
        dead
    );
}

#[test]
fn guarded_reachability_does_not_lower_guard_expression() {
    let unsupported_guard = Expr::Call(Box::new(sp(Expr::Var("opaque".to_string()))), vec![]);
    let reachable = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row_with_guard_expr(vec![Pattern::Wildcard], 0, unsupported_guard),
            row(vec![Pattern::Wildcard], 1),
        ],
    };
    assert!(find_unreachable_rows(&reachable).is_empty());

    let inexhaustive = PatternMatrix {
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
fn guarded_reachability_compiles_once_for_many_guarded_rows() {
    let mut rows = Vec::new();
    for i in 0..64 {
        rows.push(row_with_guard_expr(
            vec![Pattern::Int(i)],
            i as BodyId,
            Expr::Call(Box::new(sp(Expr::Var("opaque".to_string()))), vec![]),
        ));
    }
    rows.push(row(vec![Pattern::Wildcard], 64));
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows,
    };

    reset_compile_count();
    assert!(find_unreachable_rows(&pattern_matrix).is_empty());
    assert_eq!(compile_count(), 1);
}

/// An unguarded wildcard still dominates later rows. Sanity check
/// the guard-aware path doesn't break the normal case.
#[test]
fn unguarded_wildcard_still_dominates() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row_with_guard(vec![Pattern::Wildcard], 0),
            row(vec![Pattern::Wildcard], 1),
            row(vec![Pattern::Int(42)], 2),
        ],
    };
    let dead = find_unreachable_rows(&pattern_matrix);
    assert_eq!(dead, vec![2], "row 2 should be unreachable past row 1");
}

/// A guarded row whose pattern is fully covered by an unguarded
/// predecessor IS unreachable (the predecessor's pattern matches
/// every value the guarded row could see).
#[test]
fn guarded_row_unreachable_under_unguarded_cover() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row(vec![Pattern::Wildcard], 0),
            row_with_guard(vec![Pattern::Wildcard], 1),
        ],
    };
    let dead = find_unreachable_rows(&pattern_matrix);
    assert_eq!(dead, vec![1]);
}

#[test]
fn all_reachable_rows_no_warnings() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row(vec![Pattern::Int(0)], 0),
            row(vec![Pattern::Int(1)], 1),
            row(vec![Pattern::Wildcard], 2),
        ],
    };
    assert!(find_unreachable_rows(&pattern_matrix).is_empty());
}

#[test]
fn distinct_utf8_binary_literals_are_reachable() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row(vec![Pattern::Binary(b"hi".to_vec())], 0),
            row(vec![Pattern::Binary(b"bye".to_vec())], 1),
            row(vec![Pattern::Wildcard], 2),
        ],
    };

    assert!(find_unreachable_rows(&pattern_matrix).is_empty());
    assert!(!is_inexhaustive(&pattern_matrix));
}

#[test]
fn distinct_float_literals_are_reachable() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row(vec![Pattern::Float(1.5)], 0),
            row(vec![Pattern::Float(2.5)], 1),
            row(vec![Pattern::Wildcard], 2),
        ],
    };

    assert!(find_unreachable_rows(&pattern_matrix).is_empty());
    assert!(!is_inexhaustive(&pattern_matrix));
}

#[test]
fn duplicate_float_literal_is_unreachable() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row(vec![Pattern::Float(1.5)], 0),
            row(vec![Pattern::Float(1.5)], 1),
        ],
    };

    assert_eq!(find_unreachable_rows(&pattern_matrix), vec![1]);
}

#[test]
fn duplicate_utf8_binary_literal_is_unreachable() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row(vec![Pattern::Binary(b"hi".to_vec())], 0),
            row(vec![Pattern::Binary(b"hi".to_vec())], 1),
        ],
    };

    assert_eq!(find_unreachable_rows(&pattern_matrix), vec![1]);
}

#[test]
fn utf8_binary_literals_without_wildcard_are_inexhaustive() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row(vec![Pattern::Binary(b"hi".to_vec())], 0),
            row(vec![Pattern::Binary(b"bye".to_vec())], 1),
        ],
    };

    assert!(is_inexhaustive(&pattern_matrix));
}

#[test]
fn inexhaustive_no_wildcard_flagged() {
    // Two specific ints, no wildcard → default reaches Fail.
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![row(vec![Pattern::Int(0)], 0), row(vec![Pattern::Int(1)], 1)],
    };
    assert!(is_inexhaustive(&pattern_matrix));
}

#[test]
fn exhaustive_with_wildcard_not_flagged() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row(vec![Pattern::Int(0)], 0),
            row(vec![Pattern::Wildcard], 1),
        ],
    };
    assert!(!is_inexhaustive(&pattern_matrix));
}

#[test]
fn empty_list_and_cons_exhaust_list_domain() {
    let cons = Pattern::List(
        vec![sp(Pattern::Var("h".to_string()))],
        Some(Box::new(sp(Pattern::Var("t".to_string())))),
    );
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row(vec![Pattern::List(vec![], None)], 0),
            row(vec![cons], 1),
        ],
    };
    assert!(!is_inexhaustive_with_domains(
        &pattern_matrix,
        &[SubjectDomain::List]
    ));
}

#[test]
fn empty_list_and_cons_do_not_exhaust_any_domain() {
    let cons = Pattern::List(
        vec![sp(Pattern::Var("h".to_string()))],
        Some(Box::new(sp(Pattern::Var("t".to_string())))),
    );
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row(vec![Pattern::List(vec![], None)], 0),
            row(vec![cons], 1),
        ],
    };
    assert!(is_inexhaustive_with_domains(
        &pattern_matrix,
        &[SubjectDomain::Any]
    ));
}

#[test]
fn pattern_matrix_var_leaf_preserves_binding() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(42)],
        rows: vec![row(vec![Pattern::Var("x".to_string())], 7)],
    };
    let matcher = compile_pattern_matrix(pattern_matrix).expect("compile pattern matrix");
    let Some(crate::matcher::MatcherNode::Leaf(leaf)) = matcher.node(matcher.root) else {
        panic!("expected root leaf, got {:?}", matcher.node(matcher.root));
    };

    assert_eq!(leaf.body_id, 7);
    assert_eq!(leaf.bindings.len(), 1);
    assert_eq!(leaf.bindings[0].name, "x");
    assert_eq!(
        leaf.bindings[0].source,
        crate::matcher::SubjectRef::Input(crate::matcher::InputId(0))
    );
}

#[test]
fn pattern_matrix_tuple_switch_preserves_shape_and_field_binding() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![row(
            vec![Pattern::Tuple(vec![
                sp(Pattern::Atom("ok".to_string())),
                sp(Pattern::Var("x".to_string())),
            ])],
            3,
        )],
    };
    let matcher = compile_pattern_matrix(pattern_matrix).expect("compile pattern matrix");
    let Some(crate::matcher::MatcherNode::Switch { kind, cases, .. }) =
        matcher.node(matcher.root)
    else {
        panic!("expected root switch, got {:?}", matcher.node(matcher.root));
    };

    assert_eq!(*kind, crate::matcher::SwitchKind::TupleArity);
    assert_eq!(cases[0].0, crate::matcher::SwitchKey::Arity(2));
    let arity_node = cases[0].1;
    let Some(crate::matcher::MatcherNode::Switch {
        kind,
        cases: atom_cases,
        ..
    }) = matcher.node(arity_node)
    else {
        panic!(
            "expected nested atom switch, got {:?}",
            matcher.node(arity_node)
        );
    };
    assert_eq!(*kind, crate::matcher::SwitchKind::Atom);
    assert_eq!(
        atom_cases[0].0,
        crate::matcher::SwitchKey::AtomName("ok".to_string())
    );
    let Some(crate::matcher::MatcherNode::Leaf(leaf)) = matcher.node(atom_cases[0].1) else {
        panic!(
            "expected atom leaf, got {:?}",
            matcher.node(atom_cases[0].1)
        );
    };
    assert_eq!(
        leaf.bindings[0].source,
        crate::matcher::SubjectRef::TupleField {
            tuple: Box::new(crate::matcher::SubjectRef::Input(crate::matcher::InputId(
                0
            ))),
            index: 1,
        }
    );
}

#[test]
fn pattern_matrix_tuple_default_preserves_removed_column_binding() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(2)],
        rows: vec![
            row(
                vec![Pattern::Tuple(vec![
                    sp(Pattern::Atom("ok".to_string())),
                    sp(Pattern::Wildcard),
                ])],
                0,
            ),
            row(vec![Pattern::Var("fallback".to_string())], 1),
        ],
    };
    let matcher = compile_pattern_matrix(pattern_matrix).expect("compile pattern matrix");
    let Some(crate::matcher::MatcherNode::Switch { default, .. }) = matcher.node(matcher.root)
    else {
        panic!(
            "expected tuple switch, got {:?}",
            matcher.node(matcher.root)
        );
    };
    let Some(crate::matcher::MatcherNode::Leaf(leaf)) = matcher.node(*default) else {
        panic!("expected default leaf, got {:?}", matcher.node(*default));
    };

    assert_eq!(leaf.body_id, 1);
    assert_eq!(leaf.bindings.len(), 1);
    assert_eq!(leaf.bindings[0].name, "fallback");
    assert_eq!(
        leaf.bindings[0].source,
        crate::matcher::SubjectRef::Input(crate::matcher::InputId(0))
    );
}

#[test]
fn pattern_matrix_list_cons_preserves_head_tail_refs() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(3)],
        rows: vec![row(
            vec![Pattern::List(
                vec![sp(Pattern::Var("h".to_string()))],
                Some(Box::new(sp(Pattern::Var("t".to_string())))),
            )],
            0,
        )],
    };
    let matcher = compile_pattern_matrix(pattern_matrix).expect("compile pattern matrix");
    let Some(crate::matcher::MatcherNode::Switch { cases, .. }) = matcher.node(matcher.root)
    else {
        panic!("expected list switch, got {:?}", matcher.node(matcher.root));
    };
    let (_, cons_node) = cases
        .iter()
        .find(|(key, _)| *key == crate::matcher::SwitchKey::Cons)
        .expect("cons case");
    let Some(crate::matcher::MatcherNode::Leaf(leaf)) = matcher.node(*cons_node) else {
        panic!("expected cons leaf, got {:?}", matcher.node(*cons_node));
    };

    assert_eq!(
        leaf.bindings[0].source,
        crate::matcher::SubjectRef::ListHead(Box::new(crate::matcher::SubjectRef::Input(
            crate::matcher::InputId(0),
        )))
    );
    assert_eq!(
        leaf.bindings[1].source,
        crate::matcher::SubjectRef::ListTail(Box::new(crate::matcher::SubjectRef::Input(
            crate::matcher::InputId(0),
        )))
    );
}

#[test]
fn pattern_matrix_list_default_preserves_removed_column_binding() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(4)],
        rows: vec![
            row(
                vec![Pattern::List(
                    vec![sp(Pattern::Var("head".to_string()))],
                    Some(Box::new(sp(Pattern::Var("tail".to_string())))),
                )],
                0,
            ),
            row(vec![Pattern::Var("fallback".to_string())], 1),
        ],
    };
    let matcher = compile_pattern_matrix(pattern_matrix).expect("compile pattern matrix");
    let Some(crate::matcher::MatcherNode::Switch { default, .. }) = matcher.node(matcher.root)
    else {
        panic!("expected list switch, got {:?}", matcher.node(matcher.root));
    };
    let Some(crate::matcher::MatcherNode::Leaf(leaf)) = matcher.node(*default) else {
        panic!("expected default leaf, got {:?}", matcher.node(*default));
    };

    assert_eq!(leaf.body_id, 1);
    assert_eq!(leaf.bindings.len(), 1);
    assert_eq!(leaf.bindings[0].name, "fallback");
    assert_eq!(
        leaf.bindings[0].source,
        crate::matcher::SubjectRef::Input(crate::matcher::InputId(0))
    );
}

#[test]
fn pattern_matrix_lowers_guard_to_guard_node() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row_with_guard(vec![Pattern::Wildcard], 0),
            row(vec![Pattern::Wildcard], 1),
        ],
    };
    let matcher = compile_pattern_matrix(pattern_matrix).expect("compile guarded matcher");
    let Some(crate::matcher::MatcherNode::Guard {
        expr,
        on_true,
        on_false,
        ..
    }) = matcher.node(matcher.root)
    else {
        panic!("expected guard root, got {:?}", matcher.node(matcher.root));
    };
    assert!(matches!(
        expr,
        crate::matcher::GuardExpr::Const(crate::matcher::MatcherConst::Bool(true))
    ));
    let Some(crate::matcher::MatcherNode::Leaf(true_leaf)) = matcher.node(*on_true) else {
        panic!("expected guard true leaf, got {:?}", matcher.node(*on_true));
    };
    assert_eq!(true_leaf.body_id, 0);
    let Some(crate::matcher::MatcherNode::Leaf(false_leaf)) = matcher.node(*on_false) else {
        panic!(
            "expected guard false fallthrough leaf, got {:?}",
            matcher.node(*on_false)
        );
    };
    assert_eq!(false_leaf.body_id, 1);
}

#[test]
fn pattern_matrix_guard_capture_walks_call_args_without_capturing_callee() {
    let guard = Expr::Call(
        Box::new(sp(Expr::Var("positive".to_string()))),
        vec![sp(Expr::BinOp(
            crate::ast::BinOp::Add,
            Box::new(sp(Expr::Var("x".to_string()))),
            Box::new(sp(Expr::Var("limit".to_string()))),
        ))],
    );
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row_with_guard_expr(vec![Pattern::Var("x".to_string())], 0, guard),
            row(vec![Pattern::Wildcard], 1),
        ],
    };
    let mut resolver = |_name: &str, _arity: usize, _args: Vec<crate::matcher::GuardExpr>| {
        Ok(Some(crate::matcher::GuardExpr::Const(
            crate::matcher::MatcherConst::Bool(true),
        )))
    };
    let matcher = compile_pattern_matrix_with_guard_resolver(pattern_matrix, &mut resolver)
        .expect("compile matcher");

    assert_eq!(matcher.pinned.len(), 1);
    assert_eq!(matcher.pinned[0].name, "limit");
}

#[test]
fn pattern_matrix_lowers_pinned_per_row_to_eq_pinned_test() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row(vec![Pattern::Pinned("want".to_string())], 0),
            row(vec![Pattern::Wildcard], 1),
        ],
    };
    let matcher = compile_pattern_matrix(pattern_matrix).expect("compile pattern matrix");

    assert_eq!(matcher.pinned.len(), 1);
    assert_eq!(matcher.pinned[0].name, "want");
    let Some(crate::matcher::MatcherNode::Test {
        test,
        on_true,
        on_false,
        ..
    }) = matcher.node(matcher.root)
    else {
        panic!(
            "expected pinned test root, got {:?}",
            matcher.node(matcher.root)
        );
    };
    assert_eq!(
        *test,
        crate::matcher::MatcherTest::EqPinned {
            subject: crate::matcher::SubjectRef::Input(crate::matcher::InputId(0)),
            pinned: crate::matcher::PinnedId(0),
        }
    );
    assert!(matches!(
        matcher.node(*on_true),
        Some(crate::matcher::MatcherNode::Leaf(
            crate::matcher::MatcherLeaf { body_id: 0, .. }
        ))
    ));
    assert!(matches!(
        matcher.node(*on_false),
        Some(crate::matcher::MatcherNode::Leaf(
            crate::matcher::MatcherLeaf { body_id: 1, .. }
        ))
    ));
}

#[test]
fn pattern_matrix_lowers_tuple_field_pinned_with_var_binding() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![row(
            vec![Pattern::Tuple(vec![
                sp(Pattern::Atom("reply".to_string())),
                sp(Pattern::Pinned("ref".to_string())),
                sp(Pattern::Var("payload".to_string())),
            ])],
            0,
        )],
    };
    let matcher = compile_pattern_matrix(pattern_matrix).expect("compile pattern matrix");
    let pinned_test = matcher
        .nodes
        .iter()
        .find_map(|node| match node {
            crate::matcher::MatcherNode::Test {
                test: test @ crate::matcher::MatcherTest::EqPinned { .. },
                ..
            } => Some(test),
            _ => None,
        })
        .expect("pinned test");

    assert_eq!(matcher.pinned[0].name, "ref");
    assert_eq!(
        *pinned_test,
        crate::matcher::MatcherTest::EqPinned {
            subject: crate::matcher::SubjectRef::TupleField {
                tuple: Box::new(crate::matcher::SubjectRef::Input(crate::matcher::InputId(
                    0
                ))),
                index: 1,
            },
            pinned: crate::matcher::PinnedId(0),
        }
    );
    let payload_binding = matcher.nodes.iter().find_map(|node| match node {
        crate::matcher::MatcherNode::Leaf(leaf) => leaf
            .bindings
            .iter()
            .find(|binding| binding.name == "payload"),
        _ => None,
    });
    assert_eq!(
        payload_binding.map(|binding| binding.source.clone()),
        Some(crate::matcher::SubjectRef::TupleField {
            tuple: Box::new(crate::matcher::SubjectRef::Input(crate::matcher::InputId(
                0
            ))),
            index: 2,
        })
    );
}

#[test]
fn pattern_matrix_lowers_empty_map_to_map_kind_test() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![
            row(vec![Pattern::Map(vec![])], 0),
            row(vec![Pattern::Wildcard], 1),
        ],
    };
    let matcher = compile_pattern_matrix(pattern_matrix).expect("compile pattern matrix");

    let Some(crate::matcher::MatcherNode::Test {
        test,
        on_true,
        on_false,
        ..
    }) = matcher.node(matcher.root)
    else {
        panic!(
            "expected map-kind test root, got {:?}",
            matcher.node(matcher.root)
        );
    };
    assert_eq!(
        *test,
        crate::matcher::MatcherTest::MapKind {
            subject: crate::matcher::SubjectRef::Input(crate::matcher::InputId(0)),
        }
    );
    assert!(matches!(
        matcher.node(*on_true),
        Some(crate::matcher::MatcherNode::Leaf(
            crate::matcher::MatcherLeaf { body_id: 0, .. }
        ))
    ));
    assert!(matches!(
        matcher.node(*on_false),
        Some(crate::matcher::MatcherNode::Leaf(
            crate::matcher::MatcherLeaf { body_id: 1, .. }
        ))
    ));
}

#[test]
fn pattern_matrix_lowers_scalar_map_key_to_has_key_and_value_subject() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![row(
            vec![Pattern::Map(vec![(
                sp(Pattern::Atom("id".to_string())),
                sp(Pattern::Int(42)),
            )])],
            0,
        )],
    };
    let matcher = compile_pattern_matrix(pattern_matrix).expect("compile pattern matrix");
    assert_eq!(
        matcher.prepared_keys,
        vec![crate::matcher::MatcherConst::AtomName("id".to_string())]
    );
    let map_key = crate::matcher::MatcherConst::PreparedKey(0);

    assert!(matcher.nodes.iter().any(|node| matches!(
        node,
        crate::matcher::MatcherNode::Test {
            test: crate::matcher::MatcherTest::MapHasKey {
                subject: crate::matcher::SubjectRef::Input(crate::matcher::InputId(0)),
                key,
            },
            ..
        } if *key == map_key
    )));
    assert!(matcher.nodes.iter().any(|node| matches!(
        node,
        crate::matcher::MatcherNode::Test {
            test: crate::matcher::MatcherTest::EqConst {
                subject: crate::matcher::SubjectRef::MapValue { map, key },
                value: crate::matcher::MatcherConst::Int(42),
            },
            ..
        } if **map == crate::matcher::SubjectRef::Input(crate::matcher::InputId(0))
            && *key == map_key
    )));
}

#[test]
fn pattern_matrix_checks_key_presence_before_matching_nil_value() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![row(
            vec![Pattern::Map(vec![(sp(Pattern::Int(7)), sp(Pattern::Nil))])],
            0,
        )],
    };
    let matcher = compile_pattern_matrix(pattern_matrix).expect("compile pattern matrix");

    let Some(crate::matcher::MatcherNode::Test {
        test: crate::matcher::MatcherTest::MapKind { .. },
        on_true: has_key,
        ..
    }) = matcher.node(matcher.root)
    else {
        panic!(
            "expected map-kind root, got {:?}",
            matcher.node(matcher.root)
        );
    };
    let Some(crate::matcher::MatcherNode::Test {
        test: crate::matcher::MatcherTest::MapHasKey { .. },
        on_true: value_test,
        ..
    }) = matcher.node(*has_key)
    else {
        panic!("expected map-has-key after kind test");
    };
    assert!(matches!(
        matcher.node(*value_test),
        Some(crate::matcher::MatcherNode::Test {
            test: crate::matcher::MatcherTest::EqConst {
                subject: crate::matcher::SubjectRef::MapValue { .. },
                value: crate::matcher::MatcherConst::Nil,
            },
            ..
        })
    ));
}

#[test]
fn pattern_matrix_lowers_heap_map_keys_to_prepared_slots() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![row(
            vec![Pattern::Map(vec![(
                sp(Pattern::Binary(b"id".to_vec())),
                sp(Pattern::Wildcard),
            )])],
            0,
        )],
    };
    let matcher = compile_pattern_matrix(pattern_matrix).expect("compile pattern matrix");
    assert_eq!(
        matcher.prepared_keys,
        vec![crate::matcher::MatcherConst::Utf8Binary(b"id".to_vec())]
    );
    assert!(matcher.nodes.iter().any(|node| matches!(
        node,
        crate::matcher::MatcherNode::Test {
            test: crate::matcher::MatcherTest::MapHasKey {
                key: crate::matcher::MatcherConst::PreparedKey(0),
                ..
            },
            ..
        }
    )));
}

#[test]
fn pattern_matrix_lowers_empty_bitstring_to_bitstring_test() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![row(vec![Pattern::Bitstring(vec![])], 0)],
    };
    let matcher = compile_pattern_matrix(pattern_matrix).expect("compile pattern matrix");

    let Some(crate::matcher::MatcherNode::Test {
        test: crate::matcher::MatcherTest::Bitstring { subject, fields },
        ..
    }) = matcher.node(matcher.root)
    else {
        panic!(
            "expected bitstring test root, got {:?}",
            matcher.node(matcher.root)
        );
    };
    assert_eq!(
        *subject,
        crate::matcher::SubjectRef::Input(crate::matcher::InputId(0))
    );
    assert!(fields.is_empty());
}

#[test]
fn pattern_matrix_lowers_bitstring_field_specs_and_bindings() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![row(
            vec![Pattern::Bitstring(vec![crate::ast::BitField {
                value: sp(Pattern::Var("byte".to_string())),
                spec: crate::ast::BitFieldSpec {
                    ty: crate::ast::BitType::Integer,
                    size: Some(crate::ast::BitSize::Literal(8)),
                    endian: crate::ast::Endian::Little,
                    signed: true,
                    unit: Some(1),
                },
            }])],
            0,
        )],
    };
    let matcher = compile_pattern_matrix(pattern_matrix).expect("compile pattern matrix");

    let Some(crate::matcher::MatcherNode::Test {
        test: crate::matcher::MatcherTest::Bitstring { fields, .. },
        ..
    }) = matcher.node(matcher.root)
    else {
        panic!("expected bitstring root");
    };
    assert_eq!(
        fields,
        &vec![crate::matcher::MatcherBitField {
            ty: crate::matcher::MatcherBitType::Integer,
            size: Some(crate::matcher::MatcherBitSize::Literal(8)),
            endian: crate::matcher::MatcherEndian::Little,
            signed: true,
            unit: Some(1),
            direct_bindings: vec!["byte".to_string()],
        }]
    );
    let byte_binding = matcher.nodes.iter().find_map(|node| match node {
        crate::matcher::MatcherNode::Leaf(leaf) => {
            leaf.bindings.iter().find(|binding| binding.name == "byte")
        }
        _ => None,
    });
    assert_eq!(
        byte_binding.map(|binding| binding.source.clone()),
        Some(crate::matcher::SubjectRef::BitstringField {
            bitstring: Box::new(crate::matcher::SubjectRef::Input(crate::matcher::InputId(
                0
            ))),
            index: 0,
        })
    );
}

#[test]
fn pattern_matrix_lowers_dynamic_bitstring_size_by_binding_name() {
    let pattern_matrix = PatternMatrix {
        subjects: vec![Var(0)],
        rows: vec![row(
            vec![Pattern::Bitstring(vec![
                crate::ast::BitField {
                    value: sp(Pattern::Var("n".to_string())),
                    spec: crate::ast::BitFieldSpec {
                        size: Some(crate::ast::BitSize::Literal(8)),
                        ..Default::default()
                    },
                },
                crate::ast::BitField {
                    value: sp(Pattern::Var("payload".to_string())),
                    spec: crate::ast::BitFieldSpec {
                        ty: crate::ast::BitType::Binary,
                        size: Some(crate::ast::BitSize::Var("n".to_string())),
                        ..Default::default()
                    },
                },
            ])],
            0,
        )],
    };
    let matcher = compile_pattern_matrix(pattern_matrix).expect("compile pattern matrix");

    let Some(crate::matcher::MatcherNode::Test {
        test: crate::matcher::MatcherTest::Bitstring { fields, .. },
        ..
    }) = matcher.node(matcher.root)
    else {
        panic!("expected bitstring root");
    };
    assert_eq!(
        fields[1].size,
        Some(crate::matcher::MatcherBitSize::BindingName("n".to_string()))
    );
}
