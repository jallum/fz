//! fz-ul4.10.1 — AST reification.
//!
//! Round-trip encoding from `Expr` to fz `Value` and back, used by `quote`
//! (.10.2) and the macro expansion pass (.10.3). Modeled after Elixir's
//! quoted form: literals are self-quoting, vars/calls/operators reify as
//! 3-tuples `{name :: atom, meta :: map, args :: list | atom}`. Other
//! tuples are wrapped under `:"{}"` so they can't be confused with AST
//! 3-tuples.
//!
//! v1 scope (this subticket): literals, Var, Call, BinOp, UnOp, List,
//! Tuple, Block, If, Match (restricted to Pattern::Var on the LHS).
//! Constructs outside this subset return an error rather than silently
//! producing something the decoder can't recover. Larger constructs
//! (Case/Cond/With/Lambda/Maps/Bitstrings/VecLits/cons-tail List/general
//! Pattern) get filed as follow-up if .10.3 needs them.
//!
//! Span policy (post-.20.2): `expr_to_value` ignores spans (Values are
//! span-less runtime data). `value_to_expr` produces `Span::DUMMY` on
//! every decoded node — `.20.3` is responsible for stamping
//! `SpanOrigin::Expanded` lineage at the macro call site.
//!
//! Examples:
//!   42                  -> Value::Int(42)
//!   :ok                 -> Value::Atom("ok")
//!   x                   -> {:x, %{}, :user}
//!   1 + 2               -> {:+, %{}, [1, 2]}
//!   f(a, b)             -> {:f, %{}, [{:a,_,_}, {:b,_,_}]}
//!   [1, 2]              -> [1, 2]                 (real fz list)
//!   {1, 2}              -> {1, 2}                 (real 2-tuple)
//!   {1, 2, 3}           -> {:"{}", %{}, [1, 2, 3]} (wrapped: 3-tuple AST shape reserved)
//!   if c, do: t, else:e -> {:if, %{}, [c, [{:do, t}, {:else, e}]]}
//!   x = 1               -> {:=, %{}, [{:x,_,_}, 1]}

use crate::ast::*;
use crate::value::{FzMap, Value};
use std::rc::Rc;

const USER_CTX: &str = "user";

/// Reify a Spanned<Expr> to a Value. Spans are dropped — Values are runtime
/// data and carry no syntax position.
pub fn expr_to_value(e: &Spanned<Expr>) -> Result<Value, String> {
    Ok(match &e.node {
        Expr::Int(n) => Value::Int(*n),
        Expr::Float(f) => Value::Float(*f),
        Expr::Bool(b) => Value::Bool(*b),
        Expr::Nil => Value::Nil,
        Expr::Atom(s) => Value::Atom(Rc::from(s.as_str())),
        Expr::Binary(bytes) => Value::Binary(Rc::from(bytes.as_slice())),

        Expr::Var(name) => ast_node(name, &[], Some(atom(USER_CTX))),

        // fz-swt.5: `&name/arity` reifies as `:&(:name, :arity)` — an
        // AST node so it round-trips through quote/unquote like any other
        // leaf. The decode side is not implemented for this v1 reifier.
        Expr::FnRef { name, arity } => ast_node(
            "&",
            &[],
            Some(Value::List(Rc::new(vec![
                Value::Atom(Rc::from(name.as_str())),
                Value::Int(*arity as i64),
            ]))),
        ),

        Expr::List(xs, tail) => {
            if tail.is_some() {
                return Err("quote: list cons-tail not yet supported".into());
            }
            Value::List(Rc::new(reify_each(xs)?))
        }

        Expr::Tuple(xs) => {
            let reified = reify_each(xs)?;
            if reified.len() == 2 {
                Value::Tuple(Rc::new(reified))
            } else {
                ast_node("{}", &[], Some(Value::List(Rc::new(reified))))
            }
        }

        Expr::Call(callee, args) => {
            let name = match &callee.node {
                Expr::Var(n) => n.clone(),
                _ => return Err("quote: only direct named calls supported in v1".into()),
            };
            let arg_vs = reify_each(args)?;
            ast_node(&name, &[], Some(Value::List(Rc::new(arg_vs))))
        }

        Expr::BinOp(op, l, r) => {
            let lv = expr_to_value(l)?;
            let rv = expr_to_value(r)?;
            ast_node(
                binop_atom(*op),
                &[],
                Some(Value::List(Rc::new(vec![lv, rv]))),
            )
        }

        Expr::UnOp(op, x) => {
            let xv = expr_to_value(x)?;
            ast_node(unop_atom(*op), &[], Some(Value::List(Rc::new(vec![xv]))))
        }

        Expr::Block(xs) => {
            let reified = reify_each(xs)?;
            ast_node("__block__", &[], Some(Value::List(Rc::new(reified))))
        }

        Expr::If(c, t, els) => {
            let cv = expr_to_value(c)?;
            let tv = expr_to_value(t)?;
            let mut kw = vec![kv("do", tv)];
            if let Some(e) = els {
                kw.push(kv("else", expr_to_value(e)?));
            }
            ast_node(
                "if",
                &[],
                Some(Value::List(Rc::new(vec![cv, Value::List(Rc::new(kw))]))),
            )
        }

        Expr::Match(pat, rhs) => {
            let lhs = match &pat.node {
                Pattern::Var(n) => ast_node(n, &[], Some(atom(USER_CTX))),
                _ => return Err("quote: only Pattern::Var on lhs of `=` in v1".into()),
            };
            let rv = expr_to_value(rhs)?;
            ast_node("=", &[], Some(Value::List(Rc::new(vec![lhs, rv]))))
        }

        Expr::Quote(_) | Expr::Unquote(_) => {
            return Err("ast_value: quote/unquote must be evaluated, not reified".into());
        }
        Expr::Case(_, _)
        | Expr::Cond(_)
        | Expr::With(_, _, _)
        | Expr::Receive { .. }
        | Expr::Lambda(_, _)
        | Expr::Map(_)
        | Expr::MapUpdate(_, _)
        | Expr::Index(_, _)
        | Expr::VecLit(_, _)
        | Expr::Bitstring(_) => {
            return Err(format!(
                "quote: unsupported expr variant in v1: {:?}",
                e.node
            ));
        }
    })
}

/// Decode a reified Value back to a Spanned<Expr>. Every node has
/// `span = Span::DUMMY` — the caller (.20.3) is responsible for stamping
/// `SpanOrigin::Expanded` lineage at the macro call site.
pub fn value_to_expr(v: &Value) -> Result<Spanned<Expr>, String> {
    Ok(Spanned::dummy(value_to_expr_inner(v)?))
}

fn value_to_expr_inner(v: &Value) -> Result<Expr, String> {
    match v {
        Value::Int(n) => Ok(Expr::Int(*n)),
        Value::Float(f) => Ok(Expr::Float(*f)),
        Value::Bool(b) => Ok(Expr::Bool(*b)),
        Value::Nil => Ok(Expr::Nil),
        Value::Atom(s) => Ok(Expr::Atom(s.to_string())),
        Value::Binary(s) => Ok(Expr::Binary(s.to_vec())),

        Value::List(xs) => {
            let exprs = xs
                .iter()
                .map(value_to_expr)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Expr::List(exprs, None))
        }

        Value::Tuple(elems) if elems.len() == 2 => Ok(Expr::Tuple(vec![
            value_to_expr(&elems[0])?,
            value_to_expr(&elems[1])?,
        ])),

        Value::Tuple(elems) if elems.len() == 3 => decode_ast_node(&elems[0], &elems[2]),

        Value::Tuple(elems) => Err(format!(
            "decode: tuple of arity {} is neither a literal tuple nor an AST node \
             (AST nodes are 3-tuples; non-2 literal tuples must be wrapped under :\"{{}}\")",
            elems.len()
        )),

        other => Err(format!("decode: cannot convert {:?} to Expr", other.kind())),
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn atom(s: &str) -> Value {
    Value::Atom(Rc::from(s))
}

fn ast_node(name: &str, _meta: &[(String, Value)], args_or_ctx: Option<Value>) -> Value {
    let args = args_or_ctx.unwrap_or(atom(USER_CTX));
    Value::Tuple(Rc::new(vec![
        atom(name),
        Value::Map(Rc::new(FzMap::new())),
        args,
    ]))
}

fn kv(key: &str, val: Value) -> Value {
    Value::Tuple(Rc::new(vec![atom(key), val]))
}

fn reify_each(xs: &[Spanned<Expr>]) -> Result<Vec<Value>, String> {
    xs.iter().map(expr_to_value).collect()
}

fn decode_ast_node(head: &Value, tail: &Value) -> Result<Expr, String> {
    let name: &str = match head {
        Value::Atom(s) => s,
        _ => return Err("decode: AST node head must be an atom".into()),
    };

    if let Value::Atom(_) = tail {
        return Ok(Expr::Var(name.to_string()));
    }

    let args = match tail {
        Value::List(xs) => xs.clone(),
        _ => {
            return Err(format!(
                "decode: AST node {:?} expected list args, got {:?}",
                name,
                tail.kind()
            ));
        }
    };

    match name {
        "{}" => {
            let elems = args
                .iter()
                .map(value_to_expr)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Expr::Tuple(elems))
        }
        "__block__" => {
            let exprs = args
                .iter()
                .map(value_to_expr)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Expr::Block(exprs))
        }
        "if" => {
            if args.len() != 2 {
                return Err(format!("decode: `if` expects 2 args, got {}", args.len()));
            }
            let cond = value_to_expr(&args[0])?;
            let (t, e) = decode_if_kw(&args[1])?;
            Ok(Expr::If(Box::new(cond), Box::new(t), e.map(Box::new)))
        }
        "=" => {
            if args.len() != 2 {
                return Err(format!("decode: `=` expects 2 args, got {}", args.len()));
            }
            let pat = match value_to_expr_inner(&args[0])? {
                Expr::Var(n) => Spanned::dummy(Pattern::Var(n)),
                other => return Err(format!("decode: `=` lhs must be a var, got {:?}", other)),
            };
            let rhs = value_to_expr(&args[1])?;
            Ok(Expr::Match(pat, Box::new(rhs)))
        }
        _ => {
            if let Some(b) = binop_from_atom(name)
                && args.len() == 2
            {
                return Ok(Expr::BinOp(
                    b,
                    Box::new(value_to_expr(&args[0])?),
                    Box::new(value_to_expr(&args[1])?),
                ));
            }
            if let Some(u) = unop_from_atom(name, args.len()) {
                return Ok(Expr::UnOp(u, Box::new(value_to_expr(&args[0])?)));
            }
            let arg_exprs = args
                .iter()
                .map(value_to_expr)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Expr::Call(
                Box::new(Spanned::dummy(Expr::Var(name.to_string()))),
                arg_exprs,
            ))
        }
    }
}

fn decode_if_kw(v: &Value) -> Result<(Spanned<Expr>, Option<Spanned<Expr>>), String> {
    let entries = match v {
        Value::List(xs) => xs.clone(),
        _ => return Err("decode: `if` second arg must be a keyword list".into()),
    };
    let mut t: Option<Spanned<Expr>> = None;
    let mut e: Option<Spanned<Expr>> = None;
    for entry in entries.iter() {
        let pair = match entry {
            Value::Tuple(p) if p.len() == 2 => p,
            _ => return Err("decode: `if` keyword entry must be a 2-tuple".into()),
        };
        let key = match &pair[0] {
            Value::Atom(s) => s.to_string(),
            _ => return Err("decode: `if` keyword key must be an atom".into()),
        };
        match key.as_str() {
            "do" => t = Some(value_to_expr(&pair[1])?),
            "else" => e = Some(value_to_expr(&pair[1])?),
            other => return Err(format!("decode: unknown `if` keyword `{}`", other)),
        }
    }
    let t = t.ok_or_else(|| "decode: `if` missing `:do`".to_string())?;
    Ok((t, e))
}

pub fn binop_atom(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "rem",
        BinOp::Eq => "==",
        BinOp::Neq => "!=",
        BinOp::Lt => "<",
        BinOp::LtEq => "<=",
        BinOp::Gt => ">",
        BinOp::GtEq => ">=",
        BinOp::And => "and",
        BinOp::Or => "or",
        BinOp::Pipe => "|>",
        BinOp::Cons => "|",
    }
}

fn binop_from_atom(s: &str) -> Option<BinOp> {
    Some(match s {
        "+" => BinOp::Add,
        "-" => BinOp::Sub,
        "*" => BinOp::Mul,
        "/" => BinOp::Div,
        "rem" => BinOp::Rem,
        "==" => BinOp::Eq,
        "!=" => BinOp::Neq,
        "<" => BinOp::Lt,
        "<=" => BinOp::LtEq,
        ">" => BinOp::Gt,
        ">=" => BinOp::GtEq,
        "and" => BinOp::And,
        "or" => BinOp::Or,
        "|>" => BinOp::Pipe,
        "|" => BinOp::Cons,
        _ => return None,
    })
}

pub fn unop_atom(op: UnOp) -> &'static str {
    match op {
        UnOp::Neg => "neg",
        UnOp::Not => "not",
    }
}

fn unop_from_atom(s: &str, arity: usize) -> Option<UnOp> {
    if arity != 1 {
        return None;
    }
    match s {
        "neg" => Some(UnOp::Neg),
        "not" => Some(UnOp::Not),
        _ => None,
    }
}

impl Value {
    fn kind(&self) -> &'static str {
        match self {
            Value::Int(_) => "int",
            Value::Float(_) => "float",
            Value::Bool(_) => "bool",
            Value::Atom(_) => "atom",
            Value::Binary(_) => "binary",
            Value::Nil => "nil",
            Value::List(_) => "list",
            Value::Tuple(_) => "tuple",
            Value::Vec(_) => "vec",
            Value::BitStr(_) => "bitstring",
            Value::Map(_) => "map",
            Value::Closure(_) => "closure",
            Value::Builtin(_) => "builtin",
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    fn parse_expr(src: &str) -> Spanned<Expr> {
        let wrapped = format!("fn _t() do {} end", src);
        let toks = Lexer::new(&wrapped).tokenize().unwrap();
        let prog = Parser::new(toks).parse_program().unwrap();
        match &*prog.items[0] {
            Item::Fn(d) => match &d.clauses[0].body.node {
                Expr::Block(xs) => xs[0].clone(),
                _ => d.clauses[0].body.clone(),
            },
            Item::Module(_) | Item::Alias { .. } | Item::Import { .. } | Item::MacroCall { .. } => {
                panic!("test fixture should be a fn")
            }
        }
    }

    fn round_trip(src: &str) {
        let e = parse_expr(src);
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
            (List(x), List(y)) => {
                x.len() == y.len() && x.iter().zip(y.iter()).all(|(a, b)| value_struct_eq(a, b))
            }
            (Tuple(x), Tuple(y)) => {
                x.len() == y.len() && x.iter().zip(y.iter()).all(|(a, b)| value_struct_eq(a, b))
            }
            (Map(x), Map(y)) => {
                x.entries.len() == y.entries.len()
                    && x.entries
                        .iter()
                        .zip(y.entries.iter())
                        .all(|((k1, v1), (k2, v2))| {
                            value_struct_eq(k1, k2) && value_struct_eq(v1, v2)
                        })
            }
            _ => false,
        }
    }

    fn debug_value(v: &Value) -> String {
        format!("{}", v)
    }

    #[test]
    fn literal_int() {
        round_trip("42");
    }
    #[test]
    fn literal_float() {
        round_trip("3.14");
    }
    #[test]
    fn literal_bool() {
        round_trip("true");
    }
    #[test]
    fn literal_nil() {
        round_trip("nil");
    }
    #[test]
    fn literal_atom() {
        round_trip(":ok");
    }
    #[test]
    fn literal_binary() {
        round_trip("\"hello\"");
    }
    #[test]
    fn var() {
        round_trip("x");
    }
    #[test]
    fn list() {
        round_trip("[1, 2, 3]");
    }
    #[test]
    fn tuple_2() {
        round_trip("{1, 2}");
    }
    #[test]
    fn tuple_3() {
        round_trip("{1, 2, 3}");
    }
    #[test]
    fn binop_add() {
        round_trip("1 + 2");
    }
    #[test]
    fn binop_eq() {
        round_trip("a == b");
    }
    #[test]
    fn unop_not() {
        let e = Spanned::dummy(Expr::UnOp(
            UnOp::Not,
            Box::new(Spanned::dummy(Expr::Bool(true))),
        ));
        let v = expr_to_value(&e).unwrap();
        let e2 = value_to_expr(&v).unwrap();
        assert!(matches!(e2.node, Expr::UnOp(UnOp::Not, _)));
    }
    #[test]
    fn call() {
        round_trip("foo(1, 2)");
    }
    #[test]
    fn nested_call() {
        round_trip("foo(bar(x), 2 + 3)");
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
    #[test]
    fn if_with_else() {
        round_trip("if true, do: 1, else: 2");
    }
    #[test]
    fn match_var() {
        round_trip("x = 42");
    }
    #[test]
    fn unop_neg() {
        let e = Spanned::dummy(Expr::UnOp(
            UnOp::Neg,
            Box::new(Spanned::dummy(Expr::Int(5))),
        ));
        let v = expr_to_value(&e).unwrap();
        let e2 = value_to_expr(&v).unwrap();
        assert!(matches!(e2.node, Expr::UnOp(UnOp::Neg, _)));
    }

    #[test]
    fn unsupported_expr_errors_cleanly() {
        let e = Spanned::dummy(Expr::Lambda(vec![], Box::new(Spanned::dummy(Expr::Int(0)))));
        assert!(expr_to_value(&e).is_err());
    }

    #[test]
    fn shape_of_var_is_3_tuple() {
        let e = parse_expr("foo");
        let v = expr_to_value(&e).unwrap();
        let Value::Tuple(t) = &v else {
            panic!("expected tuple, got {:?}", debug_value(&v))
        };
        assert_eq!(t.len(), 3);
        assert!(matches!(&t[0], Value::Atom(s) if &**s == "foo"));
        assert!(matches!(&t[1], Value::Map(_)));
        assert!(matches!(&t[2], Value::Atom(s) if &**s == USER_CTX));
    }

    #[test]
    fn shape_of_binop_is_3_tuple_with_args_list() {
        let e = parse_expr("1 + 2");
        let v = expr_to_value(&e).unwrap();
        let Value::Tuple(t) = &v else {
            panic!("expected tuple")
        };
        assert_eq!(t.len(), 3);
        assert!(matches!(&t[0], Value::Atom(s) if &**s == "+"));
        let Value::List(args) = &t[2] else {
            panic!("expected list args")
        };
        assert_eq!(args.len(), 2);
    }

    #[test]
    fn three_tuple_literal_is_wrapped() {
        let e = parse_expr("{1, 2, 3}");
        let v = expr_to_value(&e).unwrap();
        let Value::Tuple(t) = &v else { panic!() };
        assert_eq!(t.len(), 3);
        assert!(matches!(&t[0], Value::Atom(s) if &**s == "{}"));
    }

    #[test]
    fn decoded_nodes_carry_dummy_span() {
        let e = parse_expr("foo(1)");
        let v = expr_to_value(&e).unwrap();
        let e2 = value_to_expr(&v).unwrap();
        assert!(
            e2.span.is_dummy(),
            "value_to_expr must produce DUMMY-spanned nodes"
        );
    }
}
