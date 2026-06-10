use super::*;
use crate::compiler::source::Span;
use crate::parser::Parser;
use crate::parser::lexer::Lexer;
use crate::telemetry::Telemetry;

fn parse_expr(src: &str, tel: &dyn Telemetry) -> Spanned<Expr> {
    let wrapped = format!("fn _t() do {} end", src);
    let toks = Lexer::with_source_name(&wrapped, "<test>").tokenize(tel).unwrap();
    let prog = Parser::new(toks).parse_program(tel).unwrap();
    match &*prog.items[0] {
        Item::Fn(d) => match &d.clauses[0].body.node {
            Expr::Block(xs) => xs[0].clone(),
            _ => d.clauses[0].body.clone(),
        },
        Item::Module(_)
        | Item::Struct(_)
        | Item::Protocol(_)
        | Item::ProtocolImpl(_)
        | Item::Alias { .. }
        | Item::Import { .. }
        | Item::MacroCall { .. } => {
            panic!("test fixture should be a fn")
        }
    }
}

fn round_trip(src: &str, tel: &dyn Telemetry) {
    let e = parse_expr(src, tel);
    let v1 = expr_to_value(&e).expect("reify");
    let e2 = value_to_expr(&v1).expect("decode");
    let v2 = expr_to_value(&e2).expect("reify²");
    assert!(
        value_struct_eq(&v1, &v2),
        "round-trip mismatch for {:?}:\n  v1 = {:?}\n  v2 = {:?}",
        src,
        debug_value(&v1),
        debug_value(&v2)
    );
}

fn value_struct_eq(a: &Value, b: &Value) -> bool {
    use Value::*;
    match (a, b) {
        (Int(x), Int(y)) => x == y,
        (Float(x), Float(y)) => x.to_bits() == y.to_bits(),
        (Bool(x), Bool(y)) => x == y,
        (Atom(x), Atom(y)) => **x == **y,
        (Binary(x), Binary(y)) => **x == **y,
        (Nil, Nil) => true,
        (List(x), List(y)) => x.len() == y.len() && x.iter().zip(y.iter()).all(|(a, b)| value_struct_eq(a, b)),
        (Tuple(x), Tuple(y)) => x.len() == y.len() && x.iter().zip(y.iter()).all(|(a, b)| value_struct_eq(a, b)),
        (Map(x), Map(y)) => {
            x.entries.len() == y.entries.len()
                && x.entries
                    .iter()
                    .zip(y.entries.iter())
                    .all(|((k1, v1), (k2, v2))| value_struct_eq(k1, k2) && value_struct_eq(v1, v2))
        }
        _ => false,
    }
}

fn debug_value(v: &Value) -> String {
    format!("{}", v)
}

// DROP: macro AST round-trip for int literal; old-world AST value encoding
#[test]
fn literal_int() {
    round_trip("42", &crate::telemetry::ConfiguredTelemetry::new());
}
// DROP: macro AST round-trip for float literal; old-world AST value encoding
#[test]
fn literal_float() {
    round_trip("3.14", &crate::telemetry::ConfiguredTelemetry::new());
}
// DROP: macro AST round-trip for bool literal; old-world AST value encoding
#[test]
fn literal_bool() {
    round_trip("true", &crate::telemetry::ConfiguredTelemetry::new());
}
// DROP: macro AST round-trip for nil literal; old-world AST value encoding
#[test]
fn literal_nil() {
    round_trip("nil", &crate::telemetry::ConfiguredTelemetry::new());
}
// DROP: macro AST round-trip for atom literal; old-world AST value encoding
#[test]
fn literal_atom() {
    round_trip(":ok", &crate::telemetry::ConfiguredTelemetry::new());
}
// DROP: macro AST round-trip for binary string; old-world AST value encoding
#[test]
fn literal_binary() {
    round_trip("\"hello\"", &crate::telemetry::ConfiguredTelemetry::new());
}
// DROP: macro AST round-trip for variable reference; old-world AST encoding
#[test]
fn var() {
    round_trip("x", &crate::telemetry::ConfiguredTelemetry::new());
}
// DROP: macro AST round-trip for list literal; old-world AST value encoding
#[test]
fn list() {
    round_trip("[1, 2, 3]", &crate::telemetry::ConfiguredTelemetry::new());
}
// DROP: macro AST round-trip for 2-tuple; old-world AST value encoding
#[test]
fn tuple_2() {
    round_trip("{1, 2}", &crate::telemetry::ConfiguredTelemetry::new());
}
// DROP: macro AST round-trip for 3-tuple wraps in node; old-world encoding
#[test]
fn tuple_3() {
    round_trip("{1, 2, 3}", &crate::telemetry::ConfiguredTelemetry::new());
}
// DROP: macro AST round-trip for add binop; old-world AST value encoding
#[test]
fn binop_add() {
    round_trip("1 + 2", &crate::telemetry::ConfiguredTelemetry::new());
}
// DROP: macro AST round-trip for equality binop; old-world AST encoding
#[test]
fn binop_eq() {
    round_trip("a == b", &crate::telemetry::ConfiguredTelemetry::new());
}

// fz-g58.2.2 — the Elixir-aligned operators have AST representations that
// round-trip through the quoted-atom reflection used by macros/quote.
// PICK: Elixir-aligned binops round-trip through quoted-atom encoding
#[test]
fn binop_atom_round_trips_elixir_operators() {
    for op in [
        BinOp::ListConcat,
        BinOp::ListSubtract,
        BinOp::BinConcat,
        BinOp::Range,
        BinOp::RangeStep,
        BinOp::In,
        BinOp::NotIn,
    ] {
        let atom = binop_atom(op);
        assert_eq!(
            binop_from_atom(atom),
            Some(op),
            "binop_atom/binop_from_atom must round-trip for {:?} (atom {:?})",
            op,
            atom
        );
    }
}
#[test]
fn unop_not() {
    let e = Spanned::dummy(Expr::UnOp(UnOp::Not, Box::new(Spanned::dummy(Expr::Bool(true)))));
    let v = expr_to_value(&e).unwrap();
    let e2 = value_to_expr(&v).unwrap();
    assert!(matches!(e2.node, Expr::UnOp(UnOp::Not, _)));
}
// DROP: macro AST round-trip for fn call; old-world AST value encoding
#[test]
fn call() {
    round_trip("foo(1, 2)", &crate::telemetry::ConfiguredTelemetry::new());
}
// DROP: macro AST round-trip for nested call; old-world AST value encoding
#[test]
fn nested_call() {
    round_trip("foo(bar(x), 2 + 3)", &crate::telemetry::ConfiguredTelemetry::new());
}
#[test]
fn block() {
    let e = Spanned::dummy(Expr::Block(vec![
        Spanned::dummy(Expr::Match(
            Spanned::dummy(Pattern::Var("x".into())),
            Box::new(Spanned::dummy(Expr::Int(1))),
        )),
        Spanned::dummy(Expr::BinOp(
            BinOp::Add,
            Box::new(Spanned::dummy(Expr::Var("x".into()))),
            Box::new(Spanned::dummy(Expr::Int(2))),
        )),
    ]));
    let v = expr_to_value(&e).unwrap();
    let e2 = value_to_expr(&v).unwrap();
    assert!(value_struct_eq(&v, &expr_to_value(&e2).unwrap()));
}
// DROP: macro AST round-trip for if-else; old-world AST value encoding
#[test]
fn if_with_else() {
    round_trip("if true, do: 1, else: 2", &crate::telemetry::ConfiguredTelemetry::new());
}
// DROP: macro AST round-trip for match assignment; old-world AST encoding
#[test]
fn match_var() {
    round_trip("x = 42", &crate::telemetry::ConfiguredTelemetry::new());
}
#[test]
fn unop_neg() {
    let e = Spanned::dummy(Expr::UnOp(UnOp::Neg, Box::new(Spanned::dummy(Expr::Int(5)))));
    let v = expr_to_value(&e).unwrap();
    let e2 = value_to_expr(&v).unwrap();
    assert!(matches!(e2.node, Expr::UnOp(UnOp::Neg, _)));
}

#[test]
fn unsupported_expr_errors_cleanly() {
    let e = Spanned::dummy(Expr::Lambda(vec![LambdaClause {
        params: vec![],
        guard: None,
        body: Spanned::dummy(Expr::Int(0)),
        span: Span::DUMMY,
    }]));
    assert!(expr_to_value(&e).is_err());
}

// DROP: macro AST var shape is 3-tuple; old-world AST value encoding
#[test]
fn shape_of_var_is_3_tuple() {
    let e = parse_expr("foo", &crate::telemetry::ConfiguredTelemetry::new());
    let v = expr_to_value(&e).unwrap();
    let Value::Tuple(t) = &v else {
        panic!("expected tuple, got {:?}", debug_value(&v))
    };
    assert_eq!(t.len(), 3);
    assert!(matches!(&t[0], Value::Atom(s) if &**s == "foo"));
    assert!(matches!(&t[1], Value::Map(_)));
    assert!(matches!(&t[2], Value::Atom(s) if &**s == USER_CTX));
}

// DROP: macro AST binop shape is 3-tuple with args list; old-world encoding
#[test]
fn shape_of_binop_is_3_tuple_with_args_list() {
    let e = parse_expr("1 + 2", &crate::telemetry::ConfiguredTelemetry::new());
    let v = expr_to_value(&e).unwrap();
    let Value::Tuple(t) = &v else { panic!("expected tuple") };
    assert_eq!(t.len(), 3);
    assert!(matches!(&t[0], Value::Atom(s) if &**s == "+"));
    let Value::List(args) = &t[2] else {
        panic!("expected list args")
    };
    assert_eq!(args.len(), 2);
}

// DROP: macro AST 3-tuple wrapped in {} node; old-world AST value encoding
#[test]
fn three_tuple_literal_is_wrapped() {
    let e = parse_expr("{1, 2, 3}", &crate::telemetry::ConfiguredTelemetry::new());
    let v = expr_to_value(&e).unwrap();
    let Value::Tuple(t) = &v else { panic!() };
    assert_eq!(t.len(), 3);
    assert!(matches!(&t[0], Value::Atom(s) if &**s == "{}"));
}

// DROP: macro AST decoded nodes carry DUMMY span; old-world AST encoding
#[test]
fn decoded_nodes_carry_dummy_span() {
    let e = parse_expr("foo(1)", &crate::telemetry::ConfiguredTelemetry::new());
    let v = expr_to_value(&e).unwrap();
    let e2 = value_to_expr(&v).unwrap();
    assert!(e2.span.is_dummy(), "value_to_expr must produce DUMMY-spanned nodes");
}
