use super::*;

#[test]
fn constructs_small_ast_free_matcher() {
    let input = MatcherInput {
        var: Some(Var(7)),
        span: Span::DUMMY,
    };
    let leaf = MatcherNode::Leaf(MatcherLeaf {
        body_id: 3,
        bindings: vec![MatcherBinding {
            name: "x".to_string(),
            source: SubjectRef::TupleField {
                tuple: Box::new(SubjectRef::Input(InputId(0))),
                index: 1,
            },
            span: Span::DUMMY,
        }],
        span: Span::DUMMY,
    });
    let matcher = Matcher::new(vec![input], leaf);

    assert_eq!(matcher.root, NodeId(0));
    let Some(MatcherNode::Leaf(leaf)) = matcher.node(matcher.root) else {
        panic!("expected root leaf");
    };
    assert_eq!(leaf.body_id, 3);
    assert_eq!(leaf.bindings[0].name, "x");
}

#[test]
fn push_node_returns_stable_node_id() {
    let mut matcher = Matcher::new(
        vec![MatcherInput {
            var: None,
            span: Span::DUMMY,
        }],
        MatcherNode::Fail { span: Span::DUMMY },
    );
    let id = matcher.push_node(MatcherNode::Leaf(MatcherLeaf {
        body_id: 9,
        bindings: Vec::new(),
        span: Span::DUMMY,
    }));

    assert_eq!(id, NodeId(1));
    assert!(matches!(
        matcher.node(id),
        Some(MatcherNode::Leaf(MatcherLeaf { body_id: 9, .. }))
    ));
}

#[test]
fn matcher_module_does_not_import_ast_payloads() {
    let src = include_str!("matcher.rs");
    assert!(!src.contains(concat!("crate", "::", "ast")));
    assert!(!src.contains(concat!("Spanned", "<", "Pattern", ">")));
    assert!(!src.contains(concat!("Spanned", "<", "Expr", ">")));
}
