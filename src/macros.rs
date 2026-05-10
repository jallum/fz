//! fz-ul4.10.3 — macro expansion pass.
//!
//! Runs between parse and type-check. Walks every fn body; when a call's
//! target is the name of a `defmacro`, the args are *reified* (not
//! evaluated) into Values, the macro body is run via the interp with its
//! params bound to those values, and the returned Value is decoded back to
//! an Expr that replaces the original call. The expanded form is then
//! re-walked so a macro can expand to another macro call.
//!
//! Hygiene is .10.4. For now, gensyms are the user's responsibility (and
//! a stack-overflow guard catches runaway expansion).

use crate::ast::*;
use crate::ast_value::{expr_to_value, value_to_expr};
use crate::eval::Interp;

const MAX_EXPANSION_DEPTH: usize = 200;

/// Expand all macro calls in `prog` in place. Builds a scratch interp from
/// the program (so macros can call other macros and regular fns), then
/// expands every non-macro fn body. Macro bodies themselves are left
/// untouched — they're meta-code, not subject to expansion.
pub fn expand_program(prog: &mut Program) -> Result<(), String> {
    let macros = collect_macros(prog);
    if macros.is_empty() { return Ok(()); }

    // Scratch interp pre-loaded with all defs (macros + fns) as closures.
    let interp = Interp::new();
    interp.load_program(prog)?;
    expand_with(prog, &interp, &macros)
}

/// Like `expand_program` but uses an interp the caller already has loaded
/// (used by the REPL, which carries macros across input lines).
pub fn expand_with(
    prog: &mut Program,
    interp: &Interp,
    macros: &std::collections::HashSet<String>,
) -> Result<(), String> {
    if macros.is_empty() { return Ok(()); }
    for item in &mut prog.items {
        // We Rc::make_mut to get an exclusive ref. At this point in the
        // pipeline the program has just been parsed and isn't shared.
        let item_mut = std::rc::Rc::make_mut(item);
        match item_mut {
            Item::Fn(def) => {
                if def.is_macro { continue; }
                for clause in &mut def.clauses {
                    expand_expr(&mut clause.body, interp, macros, 0)?;
                    if let Some(g) = &mut clause.guard {
                        expand_expr(g, interp, macros, 0)?;
                    }
                }
            }
        }
    }
    Ok(())
}

/// Collect names of all macros defined in `prog`. Also exposed for the
/// REPL, which needs to know the live macro set without re-walking the
/// program every input.
pub fn collect_macros(prog: &Program) -> std::collections::HashSet<String> {
    let mut out = std::collections::HashSet::new();
    for item in &prog.items {
        match &**item {
            Item::Fn(def) => {
                if def.is_macro { out.insert(def.name.clone()); }
            }
        }
    }
    out
}

pub fn expand_expr(
    e: &mut Expr,
    interp: &Interp,
    macros: &std::collections::HashSet<String>,
    depth: usize,
) -> Result<(), String> {
    if depth > MAX_EXPANSION_DEPTH {
        return Err(format!(
            "macro expansion exceeded {} levels (likely a runaway macro)",
            MAX_EXPANSION_DEPTH
        ));
    }

    // Macro calls are handled BEFORE recursing into args — the macro
    // receives args quoted, not expanded.
    if let Expr::Call(callee, args) = e {
        if let Expr::Var(name) = &**callee {
            if macros.contains(name) {
                let arg_vs = args.iter()
                    .map(expr_to_value)
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|e| format!("macro {} arg reification: {}", name, e))?;
                let ret = interp.call_named(name, arg_vs)
                    .map_err(|e| format!("macro {} body: {}", name, e))?;
                let new_e = value_to_expr(&ret)
                    .map_err(|e| format!("macro {} return decode: {}", name, e))?;
                *e = new_e;
                // Re-expand: the result might itself be another macro call.
                return expand_expr(e, interp, macros, depth + 1);
            }
        }
    }

    // Default: recurse into children.
    match e {
        // Leaves.
        Expr::Int(_) | Expr::Float(_) | Expr::Str(_) | Expr::Atom(_)
        | Expr::Bool(_) | Expr::Nil | Expr::Var(_) => {}

        Expr::List(xs, tail) => {
            for x in xs { expand_expr(x, interp, macros, depth)?; }
            if let Some(t) = tail { expand_expr(t, interp, macros, depth)?; }
        }
        Expr::Tuple(xs) | Expr::VecLit(_, xs) | Expr::Block(xs) => {
            for x in xs { expand_expr(x, interp, macros, depth)?; }
        }
        Expr::Bitstring(fields) => {
            for f in fields { expand_expr(&mut f.value, interp, macros, depth)?; }
        }
        Expr::Map(pairs) => {
            for (k, v) in pairs {
                expand_expr(k, interp, macros, depth)?;
                expand_expr(v, interp, macros, depth)?;
            }
        }
        Expr::MapUpdate(m, pairs) => {
            expand_expr(m, interp, macros, depth)?;
            for (k, v) in pairs {
                expand_expr(k, interp, macros, depth)?;
                expand_expr(v, interp, macros, depth)?;
            }
        }
        Expr::Index(o, i) => {
            expand_expr(o, interp, macros, depth)?;
            expand_expr(i, interp, macros, depth)?;
        }
        Expr::Call(callee, args) => {
            expand_expr(callee, interp, macros, depth)?;
            for a in args { expand_expr(a, interp, macros, depth)?; }
        }
        Expr::Dot(o, _) => expand_expr(o, interp, macros, depth)?,
        Expr::BinOp(_, l, r) => {
            expand_expr(l, interp, macros, depth)?;
            expand_expr(r, interp, macros, depth)?;
        }
        Expr::UnOp(_, x) => expand_expr(x, interp, macros, depth)?,
        Expr::If(c, t, els) => {
            expand_expr(c, interp, macros, depth)?;
            expand_expr(t, interp, macros, depth)?;
            if let Some(e) = els { expand_expr(e, interp, macros, depth)?; }
        }
        Expr::Case(scr, arms) => {
            expand_expr(scr, interp, macros, depth)?;
            for arm in arms {
                expand_expr(&mut arm.body, interp, macros, depth)?;
                if let Some(g) = &mut arm.guard { expand_expr(g, interp, macros, depth)?; }
            }
        }
        Expr::Cond(pairs) => {
            for (c, b) in pairs {
                expand_expr(c, interp, macros, depth)?;
                expand_expr(b, interp, macros, depth)?;
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            for b in bindings {
                match b {
                    WithBinding::Match(_, e) => expand_expr(e, interp, macros, depth)?,
                    WithBinding::Bare(e) => expand_expr(e, interp, macros, depth)?,
                }
            }
            expand_expr(body, interp, macros, depth)?;
            for arm in else_clauses {
                expand_expr(&mut arm.body, interp, macros, depth)?;
                if let Some(g) = &mut arm.guard { expand_expr(g, interp, macros, depth)?; }
            }
        }
        Expr::Match(_, rhs) => expand_expr(rhs, interp, macros, depth)?,
        Expr::Lambda(_, body) => expand_expr(body, interp, macros, depth)?,

        // Quote bodies are reified, not expanded — they live in the
        // meta-language, not the object language. Unquote bodies are
        // similarly left alone for v1 (a follow-up could expand them so
        // unquote(some_macro_call(x)) works).
        Expr::Quote(_) | Expr::Unquote(_) => {}
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    fn parse(src: &str) -> Program {
        let toks = Lexer::new(src).tokenize().expect("lex");
        Parser::new(toks).parse_program().expect("parse")
    }

    /// Run the full pipeline (parse → expand → eval main) and return
    /// main's return value.
    fn run(src: &str) -> crate::value::Value {
        let mut prog = parse(src);
        expand_program(&mut prog).expect("expand");
        let interp = Interp::new();
        interp.load_program(&prog).expect("load");
        interp.call_named("main", vec![]).expect("eval")
    }

    #[test]
    fn defmacro_increments_arg() {
        // Classic Elixir-shape macro: receives arg as quoted form, returns
        // a quote that adds 1 to it.
        let src = r#"
defmacro plus_one(x) do
  quote do: unquote(x) + 1
end
fn main() do
  plus_one(41)
end
"#;
        assert!(matches!(run(src), crate::value::Value::Int(42)));
    }

    #[test]
    fn macro_inside_fn_body() {
        let src = r#"
defmacro double(x) do
  quote do: unquote(x) * 2
end
fn run() do
  a = double(10)
  b = double(20)
  a + b
end
fn main() do run() end
"#;
        assert!(matches!(run(src), crate::value::Value::Int(60)));
    }

    #[test]
    fn macro_returns_a_call() {
        // Macro that splices its arg into a call to a regular fn.
        let src = r#"
fn helper(x) do x * 3 end
defmacro use_helper(x) do
  quote do: helper(unquote(x))
end
fn main() do use_helper(7) end
"#;
        assert!(matches!(run(src), crate::value::Value::Int(21)));
    }

    #[test]
    fn nested_macro_expansion() {
        // Macro M2 wraps M1's output. Expander must re-expand the result.
        let src = r#"
defmacro m1(x) do quote do: unquote(x) + 1 end
defmacro m2(x) do quote do: m1(unquote(x)) end
fn main() do m2(40) end
"#;
        assert!(matches!(run(src), crate::value::Value::Int(41)));
    }

    #[test]
    fn macro_args_are_not_pre_expanded() {
        // If macro args were expanded first, m2(m1(0)) would call m1 first
        // and m2 would see 1. Macros receive args quoted, so m2 sees the
        // AST of `m1(0)` and decides what to do with it. Here m2 just
        // splices it into its result, so the final code is `m1(0) + 5` =
        // 1 + 5 = 6.
        let src = r#"
defmacro m1(x) do quote do: unquote(x) + 1 end
defmacro m2(x) do quote do: unquote(x) + 5 end
fn main() do m2(m1(0)) end
"#;
        assert!(matches!(run(src), crate::value::Value::Int(6)));
    }

    #[test]
    fn runaway_macro_caught() {
        // A macro that expands to itself: m(x) -> m(x). Should bail at the
        // depth limit instead of overflowing the stack.
        let src = r#"
defmacro loop_m(x) do
  quote do: loop_m(unquote(x))
end
fn main() do loop_m(0) end
"#;
        let mut prog = parse(src);
        let res = expand_program(&mut prog);
        assert!(res.is_err(), "expected expansion error");
        assert!(res.unwrap_err().contains("expansion"),
            "expected message about expansion");
    }

    #[test]
    fn no_macros_is_a_noop() {
        // Pipeline without macros must not regress.
        let src = "fn main() do 1 + 2 end";
        let mut prog = parse(src);
        expand_program(&mut prog).expect("expand");
        let interp = Interp::new();
        interp.load_program(&prog).expect("load");
        let v = interp.call_named("main", vec![]).expect("eval");
        assert!(matches!(v, crate::value::Value::Int(3)));
    }
}
