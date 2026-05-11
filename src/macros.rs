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
use crate::value::Value;

const MAX_EXPANSION_DEPTH: usize = 200;

/// Expand all macro calls in `prog` in place. Builds a scratch interp from
/// the program (so macros can call other macros and regular fns), then
/// expands every non-macro fn body. Macro bodies themselves are left
/// untouched — they're meta-code, not subject to expansion.
pub fn expand_program(prog: &mut Program) -> Result<(), String> {
    // Always run the item-level pass first (it doesn't need the macros set
    // since collect_macros walks both Item::Fn and the resulting Item::Fn
    // post-splice). After items are spliced, run expression-level expansion.
    let macros = collect_macros(prog);
    if macros.is_empty() && !has_item_macro_calls(prog) {
        return Ok(());
    }

    let interp = Interp::new();
    interp.load_program(prog)?;

    // Item-level expansion: replace Item::MacroCall with whatever items
    // the macro returns. Expanded items are appended to a fresh vec; the
    // macro set may grow during this pass if a macro returns more macros
    // (rare, but possible).
    expand_items(prog, &interp, &macros)?;

    // Expression-level expansion across the (now-final) fn bodies.
    let macros = collect_macros(prog);
    expand_with(prog, &interp, &macros)
}

fn has_item_macro_calls(prog: &Program) -> bool {
    fn check_items(items: &[std::rc::Rc<Item>]) -> bool {
        items.iter().any(|it| match &**it {
            Item::MacroCall { .. } => true,
            Item::Module(m) => check_items(&m.items),
            _ => false,
        })
    }
    check_items(&prog.items)
}

/// Walk top-level items and module bodies; for each Item::MacroCall whose
/// target is a defmacro, run the macro and splice its returned items in.
fn expand_items(
    prog: &mut Program,
    interp: &Interp,
    macros: &std::collections::HashSet<String>,
) -> Result<(), String> {
    prog.items = expand_item_list(prog.items.clone(), interp, macros)?;
    Ok(())
}

fn expand_item_list(
    items: Vec<std::rc::Rc<Item>>,
    interp: &Interp,
    macros: &std::collections::HashSet<String>,
) -> Result<Vec<std::rc::Rc<Item>>, String> {
    let mut out: Vec<std::rc::Rc<Item>> = Vec::new();
    for item in items {
        match &*item {
            Item::MacroCall { name, name_span: _, args, parent_module, span: _ } => {
                if !macros.contains(name) {
                    return Err(format!(
                        "item-level call `{}(...)` is not a defmacro", name));
                }
                let arg_vs = args.iter()
                    .map(expr_to_value)
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|e| format!("macro {} arg reification: {}", name, e))?;
                let prev = interp.gensym_table.borrow_mut().take();
                *interp.gensym_table.borrow_mut() =
                    Some(std::collections::HashMap::new());
                let ret = interp.call_named(name, arg_vs);
                *interp.gensym_table.borrow_mut() = prev;
                let ret = ret.map_err(|e| format!("macro {} body: {}", name, e))?;
                let mut items = value_to_items(&ret)
                    .map_err(|e| format!("macro {} return: {}", name, e))?;
                // .16.5: when the macro was inside a defmodule body, the
                // resolver stamped the parent path. Qualify spliced fn
                // names so e.g. tests inside `defmodule MyTest do ...`
                // land as `MyTest.test_xxx`.
                if let Some(path) = parent_module {
                    for it in &mut items {
                        if let Item::Fn(def) = it {
                            def.name = format!("{}.{}", path, def.name);
                        }
                    }
                }
                for it in items {
                    out.push(std::rc::Rc::new(it));
                }
            }
            Item::Module(m) => {
                let new_items = expand_item_list(m.items.clone(), interp, macros)?;
                out.push(std::rc::Rc::new(Item::Module(ModuleDef {
                    name: m.name.clone(),
                    name_span: m.name_span,
                    items: new_items,
                    moduledoc: m.moduledoc.clone(),
                    span: m.span,
                })));
            }
            _ => out.push(item.clone()),
        }
    }
    Ok(out)
}

/// Decode a macro's return Value into one or more `Item`s.
///
/// Accepted shapes:
///
/// - `{:fn_def, name_atom, body_value}` — produces `Item::Fn` with a
///   single zero-arg clause. v1 is intentionally narrow: tests are all
///   zero-arg, and we can grow this when more shapes are needed.
/// - `Value::List([item_value, ...])` — multiple items in declaration
///   order. Each element is decoded recursively.
pub fn value_to_items(v: &Value) -> Result<Vec<Item>, String> {
    match v {
        Value::Tuple(t) if t.len() == 3 => {
            let tag = match &t[0] {
                Value::Atom(s) => s.to_string(),
                _ => return Err("expected item tag atom at tuple[0]".into()),
            };
            match tag.as_str() {
                "fn_def" => {
                    let name = match &t[1] {
                        Value::Atom(s) => s.to_string(),
                        _ => return Err(":fn_def expects an atom name".into()),
                    };
                    let body = value_to_expr(&t[2])?;
                    let span = crate::diag::Span::DUMMY;
                    Ok(vec![Item::Fn(FnDef {
                        name,
                        name_span: span,
                        clauses: vec![FnClause { params: vec![], guard: None, body, span }],
                        is_macro: false,
                        doc: None,
                        span,
                    })])
                }
                other => Err(format!("unknown item tag :{}", other)),
            }
        }
        Value::List(xs) => {
            let mut out = Vec::new();
            for x in xs.iter() {
                out.extend(value_to_items(x)?);
            }
            Ok(out)
        }
        other => Err(format!(
            "macro at item-position must return :fn_def tuple or list of items, got {:?}",
            other
        )),
    }
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
            Item::Module(_) | Item::Alias { .. } | Item::Import { .. } | Item::MacroCall { .. } => return Err(
                "expand_with: pre-resolution Item reached macro expander; \
                 resolve::flatten_modules must run first".into()),
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
            Item::Module(_) | Item::Alias { .. } | Item::Import { .. } | Item::MacroCall { .. } => {
                // Pre-flatten programs may still hit this path in tests;
                // be tolerant since post-flatten there are none.
            }
        }
    }
    out
}

pub fn expand_expr(
    e: &mut Spanned<Expr>,
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
    if let Expr::Call(callee, args) = &mut e.node {
        if let Expr::Var(name) = &callee.node {
            if macros.contains(name) {
                let arg_vs = args.iter()
                    .map(expr_to_value)
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|e| format!("macro {} arg reification: {}", name, e))?;
                let prev = interp.gensym_table.borrow_mut().take();
                *interp.gensym_table.borrow_mut() =
                    Some(std::collections::HashMap::new());
                let ret_res = interp.call_named(name, arg_vs);
                *interp.gensym_table.borrow_mut() = prev;
                let ret = ret_res
                    .map_err(|e| format!("macro {} body: {}", name, e))?;
                let new_e = value_to_expr(&ret)
                    .map_err(|e| format!("macro {} return decode: {}", name, e))?;
                // Preserve the original call's span on the synthesized
                // replacement. .20.3 will replace this with proper
                // SpanOrigin::Expanded lineage.
                let original_span = e.span;
                *e = Spanned { node: new_e.node, span: original_span };
                return expand_expr(e, interp, macros, depth + 1);
            }
        }
    }

    // Default: recurse into children.
    match &mut e.node {
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

    /// Run the full pipeline (parse → flatten → expand → eval main) and
    /// return main's return value.
    fn run(src: &str) -> crate::value::Value {
        let prog = parse(src);
        let mut prog = crate::resolve::flatten_modules(prog).expect("flatten");
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
    fn hygiene_macro_local_does_not_shadow_caller() {
        // Without hygiene, the macro's `t = 99` would clobber the
        // caller's `t`. With hygiene, the macro's `t` becomes a fresh
        // gensym so the caller's binding survives.
        let src = r#"
defmacro set_local() do
  quote do: t = 99
end
fn main() do
  t = 1
  set_local()
  t
end
"#;
        let v = run(src);
        assert!(matches!(v, crate::value::Value::Int(1)),
            "expected caller's t (1) to survive, got {:?}", v);
    }

    #[test]
    fn hygiene_unquoted_var_keeps_caller_name() {
        // Vars spliced via unquote come from the caller's evaluation
        // context — their VALUES, not their names — so hygiene doesn't
        // affect them. Here unquote(x) splices the literal 7.
        let src = r#"
defmacro emit(x) do
  quote do: unquote(x) + 1
end
fn main() do
  x = 7
  emit(x)
end
"#;
        assert!(matches!(run(src), crate::value::Value::Int(8)));
    }

    #[test]
    fn hygiene_consistent_within_one_invocation() {
        // The same macro-introduced name used twice in the body must map
        // to the SAME gensym, otherwise t = something; t + t breaks.
        let src = r#"
defmacro double_via_temp(x) do
  quote do
    t = unquote(x)
    t + t
  end
end
fn main() do
  t = 100
  double_via_temp(21)
end
"#;
        // Macro returns Block([t__hyg_N = 21, t__hyg_N + t__hyg_N]) → 42.
        // Caller's t stays at 100; macro's t__hyg_N is 21+21.
        assert!(matches!(run(src), crate::value::Value::Int(42)));
    }

    #[test]
    fn cross_module_macro_resolves_quote_against_home_module() {
        // Macro M.bump's body refers to bare `helper`. Resolution
        // qualifies it as M.helper inside the quote, so when expanded
        // into a different module's caller the spliced AST carries the
        // home-module path.
        let src = r#"
defmodule M do
  fn helper(x), do: x + 100
  defmacro bump(x) do
    quote do: helper(unquote(x))
  end
end
defmodule User do
  fn run(), do: M.bump(7)
end
fn main() do User.run() end
"#;
        // M.bump expands at compile time into M.helper(7) (a fully
        // qualified call), so the result is 107.
        assert!(matches!(run(src), crate::value::Value::Int(107)),
            "expected 107, got {:?}", run(src));
    }

    #[test]
    fn imported_macro_works_unqualified() {
        let src = r#"
defmodule M do
  defmacro bump(x), do: quote do: unquote(x) + 1
end
defmodule User do
  import M, only: [bump: 1]
  fn run(), do: bump(41)
end
fn main() do User.run() end
"#;
        assert!(matches!(run(src), crate::value::Value::Int(42)));
    }

    #[test]
    fn item_macro_produces_fn_def() {
        // `make_const(name, value)` builds a zero-arg fn that returns the
        // given value. Demonstrates the .16.3 item-producing path:
        // - top-level Item::MacroCall is parsed (.16.2),
        // - the macro returns {:fn_def, name_atom, body_expr},
        // - the expander splices in a real Item::Fn,
        // - the rest of the program can call it.
        let src = r#"
defmacro make_const(name, value) do
  {:fn_def, name, value}
end

make_const(:answer, 42)

fn main() do
  answer()
end
"#;
        assert!(matches!(run(src), crate::value::Value::Int(42)),
            "expected 42, got {:?}", run(src));
    }

    #[test]
    fn item_macro_produces_list_of_fns() {
        // Returning a list of :fn_def tuples splices multiple items.
        let src = r#"
defmacro pair(a, b) do
  [
    {:fn_def, :first, a},
    {:fn_def, :second, b}
  ]
end

pair(10, 20)

fn main() do
  first() + second()
end
"#;
        assert!(matches!(run(src), crate::value::Value::Int(30)));
    }

    #[test]
    fn item_macro_inside_defmodule_qualifies_names() {
        // .16.5: the resolver stamps the parent module path on the
        // MacroCall so the splicer can prefix the spliced fn names.
        let src = r#"
defmacro make_const(name, value) do
  {:fn_def, name, value}
end

defmodule Constants do
  make_const(:pi_ish, 314)
end

fn main() do
  Constants.pi_ish()
end
"#;
        assert!(matches!(run(src), crate::value::Value::Int(314)),
            "expected 314, got {:?}", run(src));
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
