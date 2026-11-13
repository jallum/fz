use super::LiteralTerm;
use crate::ast::{Expr, Spanned, Var};
use crate::ground_value::GroundValue;
use crate::source::Span;

fn at(node: Expr) -> Spanned<Expr> {
    Spanned::new(node, Span::DUMMY)
}

/// A default has to mean the same in every module that omits the field, so
/// only a value written out in full is one: scalars and containers of them.
#[test]
fn a_value_written_out_in_full_is_a_literal_term_and_writes_itself_back() {
    let written = Expr::Map(vec![(
        at(Expr::Atom("k".to_string())),
        at(Expr::List(
            vec![
                at(Expr::Int(1)),
                at(Expr::Float(0.5)),
                at(Expr::Binary(b"s".to_vec())),
                at(Expr::Tuple(vec![at(Expr::Bool(true)), at(Expr::Nil)])),
            ],
            None,
        )),
    )]);

    let term = LiteralTerm::of(&written).expect("a map of literals is a literal term");

    let LiteralTerm::Map(entries) = &term else {
        panic!("expected a map term, got {term:?}");
    };
    assert_eq!(entries[0].0, LiteralTerm::Ground(GroundValue::Atom("k".to_string())));
    assert_eq!(
        LiteralTerm::of(&term.expr(Span::DUMMY).node),
        Some(term),
        "the expression a term writes reads back as the same term"
    );
}

/// Anything that computes or names something depends on where it is read.
#[test]
fn an_expression_that_computes_or_names_something_is_not_a_literal_term() {
    let variable = Expr::Var(Var::user("x"));
    let cons_onto_a_tail = Expr::List(vec![at(Expr::Int(1))], Some(Box::new(at(Expr::Nil))));
    let list_holding_a_variable = Expr::List(vec![at(Expr::Int(1)), at(variable.clone())], None);

    for expr in [variable, cons_onto_a_tail, list_holding_a_variable] {
        assert_eq!(LiteralTerm::of(&expr), None, "{expr:?}");
    }
}
