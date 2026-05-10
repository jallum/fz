//! fz-ul4.18.1 — module resolution / flattening.
//!
//! Runs after parse and before macro expansion. Walks the parsed Program
//! and produces a flat Program where every fn lives under its
//! fully-qualified name (`Mod.fn` in .18.1; nested gets `A.B.fn` in
//! .18.2). Inside each module's bodies, bare references to sibling
//! fns/macros are rewritten to qualified names; cross-module
//! `Mod.fn(args)` calls (parsed as `Call(Dot(Var(Mod), "fn"), args)`)
//! also rewrite to `Call(Var("Mod.fn"), args)`.
//!
//! After this pass, downstream code (macro expansion, typer, eval, JIT,
//! AOT) can stay module-unaware: it sees one flat Program of
//! `Item::Fn`s with possibly-dotted names.
//!
//! Ungrouped top-level fns (those without an enclosing `defmodule`)
//! pass through with their bare names so existing un-modular fixtures
//! keep working.

use crate::ast::*;
use std::collections::HashSet;
use std::rc::Rc;

/// REPL helper: rewrite cross-module `Mod.fn(args)` calls in a single
/// expression. No sibling-fn rewriting (the REPL has no enclosing
/// module).
pub fn rewrite_expr_top_level(e: &mut Expr) {
    let no_siblings: HashSet<String> = HashSet::new();
    let mut intro: HashSet<String> = HashSet::new();
    let no_paths: HashSet<String> = HashSet::new();
    rewrite_expr(e, "", &no_siblings, &mut intro, &no_paths);
}

pub fn flatten_modules(prog: Program) -> Result<Program, String> {
    let module_paths = collect_module_paths(&prog);
    let mut out: Vec<Rc<Item>> = Vec::new();
    for item in &prog.items {
        match &**item {
            Item::Fn(def) => {
                let mut new_def = def.clone();
                let no_siblings: HashSet<String> = HashSet::new();
                for clause in &mut new_def.clauses {
                    let mut intro = pattern_intro(&clause.params);
                    rewrite_expr(&mut clause.body, "", &no_siblings, &mut intro, &module_paths);
                    if let Some(g) = &mut clause.guard {
                        rewrite_expr(g, "", &no_siblings, &mut intro, &module_paths);
                    }
                }
                out.push(Rc::new(Item::Fn(new_def)));
            }
            Item::Module(m) => flatten_module(m, "", &mut out, &module_paths)?,
        }
    }
    Ok(Program { items: out })
}

/// Walk the parsed program and collect the dotted path of every defmodule
/// declared anywhere. Used to resolve nested-module references like
/// `Inner.f(x)` from inside `Outer` to `Outer.Inner.f`.
fn collect_module_paths(prog: &Program) -> HashSet<String> {
    let mut out = HashSet::new();
    for item in &prog.items {
        if let Item::Module(m) = &**item {
            collect_paths_recursive(m, "", &mut out);
        }
    }
    out
}

fn collect_paths_recursive(m: &ModuleDef, parent: &str, out: &mut HashSet<String>) {
    let path = if parent.is_empty() { m.name.clone() } else { format!("{}.{}", parent, m.name) };
    out.insert(path.clone());
    for item in &m.items {
        if let Item::Module(inner) = &**item {
            collect_paths_recursive(inner, &path, out);
        }
    }
}

fn flatten_module(
    m: &ModuleDef,
    parent_path: &str,
    out: &mut Vec<Rc<Item>>,
    module_paths: &HashSet<String>,
) -> Result<(), String> {
    let module_path = if parent_path.is_empty() {
        m.name.clone()
    } else {
        format!("{}.{}", parent_path, m.name)
    };
    // Collect sibling fn/macro names so we can rewrite bare references.
    let mut siblings: HashSet<String> = HashSet::new();
    for item in &m.items {
        if let Item::Fn(def) = &**item {
            siblings.insert(def.name.clone());
        }
    }

    for item in &m.items {
        match &**item {
            Item::Fn(def) => {
                let qualified_name = format!("{}.{}", module_path, def.name);
                let mut new_def = def.clone();
                new_def.name = qualified_name;
                for clause in &mut new_def.clauses {
                    let mut intro = pattern_intro(&clause.params);
                    rewrite_expr(&mut clause.body, &module_path, &siblings, &mut intro, module_paths);
                    if let Some(g) = &mut clause.guard {
                        rewrite_expr(g, &module_path, &siblings, &mut intro, module_paths);
                    }
                }
                out.push(Rc::new(Item::Fn(new_def)));
            }
            Item::Module(inner) => {
                flatten_module(inner, &module_path, out, module_paths)?;
            }
        }
    }
    Ok(())
}

fn pattern_intro(params: &[Pattern]) -> HashSet<String> {
    let mut s = HashSet::new();
    for p in params { collect_pattern_vars(p, &mut s); }
    s
}

fn collect_pattern_vars(p: &Pattern, out: &mut HashSet<String>) {
    match p {
        Pattern::Var(n) => { out.insert(n.clone()); }
        Pattern::As(n, inner) => { out.insert(n.clone()); collect_pattern_vars(inner, out); }
        Pattern::Tuple(xs) => for x in xs { collect_pattern_vars(x, out); },
        Pattern::List(xs, tail) => {
            for x in xs { collect_pattern_vars(x, out); }
            if let Some(t) = tail { collect_pattern_vars(t, out); }
        }
        Pattern::Map(pairs) => for (_, v) in pairs { collect_pattern_vars(v, out); },
        Pattern::Bitstring(fields) => for f in fields { collect_pattern_vars(&f.value, out); },
        _ => {}
    }
}

fn rewrite_expr(
    e: &mut Expr,
    module_path: &str,
    siblings: &HashSet<String>,
    intro: &mut HashSet<String>,
    module_paths: &HashSet<String>,
) {
    match e {
        // Bare ident — if it's a sibling fn name AND not locally bound, qualify it.
        Expr::Var(n) => {
            if siblings.contains(n) && !intro.contains(n) {
                *n = format!("{}.{}", module_path, n);
            }
        }

        // Cross-module qualified call. The parser desugars `M.fn` as
        // `Index(Var("M"), Atom("fn"))` (see parser.rs Dot handling), so
        // `M.fn(args)` arrives here as `Call(Index(Var(M), Atom("fn")), args)`.
        // For nested modules, `A.B.fn(args)` lands as
        // `Call(Index(Index(Var("A"), Atom("B")), Atom("fn")), args)` —
        // we walk the chain to build the full dotted path.
        Expr::Call(callee, args) => {
            if let Some(q) = qualify_callee(callee, intro, module_path, module_paths) {
                *callee = Box::new(Expr::Var(q));
            }
            rewrite_expr(callee, module_path, siblings, intro, module_paths);
            for a in args { rewrite_expr(a, module_path, siblings, intro, module_paths); }
        }

        // Compounds: recurse, treating Match/Lambda/Case/With as scope-introducing.
        Expr::List(xs, tail) => {
            for x in xs { rewrite_expr(x, module_path, siblings, intro, module_paths); }
            if let Some(t) = tail { rewrite_expr(t, module_path, siblings, intro, module_paths); }
        }
        Expr::Tuple(xs) | Expr::VecLit(_, xs) | Expr::Block(xs) => {
            for x in xs { rewrite_expr(x, module_path, siblings, intro, module_paths); }
        }
        Expr::Bitstring(fields) => for f in fields { rewrite_expr(&mut f.value, module_path, siblings, intro, module_paths); },
        Expr::Map(pairs) => for (k, v) in pairs {
            rewrite_expr(k, module_path, siblings, intro, module_paths);
            rewrite_expr(v, module_path, siblings, intro, module_paths);
        },
        Expr::MapUpdate(m, pairs) => {
            rewrite_expr(m, module_path, siblings, intro, module_paths);
            for (k, v) in pairs {
                rewrite_expr(k, module_path, siblings, intro, module_paths);
                rewrite_expr(v, module_path, siblings, intro, module_paths);
            }
        }
        Expr::Index(o, i) => {
            rewrite_expr(o, module_path, siblings, intro, module_paths);
            rewrite_expr(i, module_path, siblings, intro, module_paths);
        }
        Expr::Dot(o, _) => rewrite_expr(o, module_path, siblings, intro, module_paths),
        Expr::BinOp(_, l, r) => {
            rewrite_expr(l, module_path, siblings, intro, module_paths);
            rewrite_expr(r, module_path, siblings, intro, module_paths);
        }
        Expr::UnOp(_, x) => rewrite_expr(x, module_path, siblings, intro, module_paths),
        Expr::If(c, t, els) => {
            rewrite_expr(c, module_path, siblings, intro, module_paths);
            rewrite_expr(t, module_path, siblings, intro, module_paths);
            if let Some(e) = els { rewrite_expr(e, module_path, siblings, intro, module_paths); }
        }
        Expr::Case(scr, arms) => {
            rewrite_expr(scr, module_path, siblings, intro, module_paths);
            for arm in arms {
                let mut nested = intro.clone();
                collect_pattern_vars(&arm.pattern, &mut nested);
                if let Some(g) = &mut arm.guard { rewrite_expr(g, module_path, siblings, &mut nested, module_paths); }
                rewrite_expr(&mut arm.body, module_path, siblings, &mut nested, module_paths);
            }
        }
        Expr::Cond(pairs) => {
            for (c, b) in pairs {
                rewrite_expr(c, module_path, siblings, intro, module_paths);
                rewrite_expr(b, module_path, siblings, intro, module_paths);
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            let mut nested = intro.clone();
            for b in bindings {
                match b {
                    WithBinding::Match(p, e) => {
                        rewrite_expr(e, module_path, siblings, &mut nested, module_paths);
                        collect_pattern_vars(p, &mut nested);
                    }
                    WithBinding::Bare(e) => rewrite_expr(e, module_path, siblings, &mut nested, module_paths),
                }
            }
            rewrite_expr(body, module_path, siblings, &mut nested, module_paths);
            for arm in else_clauses {
                let mut a_intro = intro.clone();
                collect_pattern_vars(&arm.pattern, &mut a_intro);
                if let Some(g) = &mut arm.guard { rewrite_expr(g, module_path, siblings, &mut a_intro, module_paths); }
                rewrite_expr(&mut arm.body, module_path, siblings, &mut a_intro, module_paths);
            }
        }
        Expr::Match(pat, rhs) => {
            rewrite_expr(rhs, module_path, siblings, intro, module_paths);
            collect_pattern_vars(pat, intro);
        }
        Expr::Lambda(params, body) => {
            let mut nested = intro.clone();
            for p in params { collect_pattern_vars(p, &mut nested); }
            rewrite_expr(body, module_path, siblings, &mut nested, module_paths);
        }

        // Quote bodies are reified, not resolved — they get treated literally
        // by the macro pipeline. (.18.5 may revisit cross-module macro
        // resolution.) Unquote bodies ARE regular code — recurse.
        Expr::Quote(_) => {}
        Expr::Unquote(inner) => rewrite_expr(inner, module_path, siblings, intro, module_paths),

        // Leaves.
        Expr::Int(_) | Expr::Float(_) | Expr::Str(_) | Expr::Atom(_)
        | Expr::Bool(_) | Expr::Nil => {}
    }
}

/// If `callee` is a chain of `Index(.., Atom)` / `Dot(.., name)` rooted
/// in an uppercase Var that isn't locally bound, return the dotted
/// qualified name. The leading module is interpreted relative to the
/// current `module_path` if `<current>.<leading>` is a known module
/// path; otherwise it's treated as an absolute reference.
///
/// Example: inside `Outer`, `Inner.f(x)` resolves to `Outer.Inner.f`
/// when `Outer.Inner` is a declared module, otherwise to `Inner.f`.
fn qualify_callee(
    callee: &Expr,
    intro: &HashSet<String>,
    module_path: &str,
    module_paths: &HashSet<String>,
) -> Option<String> {
    let mut path: Vec<String> = Vec::new();
    let mut cur = callee;
    loop {
        match cur {
            Expr::Index(target, key) => {
                let member = match &**key {
                    Expr::Atom(n) => n.clone(),
                    _ => return None,
                };
                path.push(member);
                cur = target;
            }
            Expr::Dot(target, member) => {
                path.push(member.clone());
                cur = target;
            }
            Expr::Var(m) if is_upper(m) && !intro.contains(m) => {
                if path.is_empty() { return None; }
                path.push(m.clone());
                path.reverse();
                let leading = &path[0];
                // Try `<current>.<leading>` as a nested-module shortcut.
                if !module_path.is_empty() {
                    let candidate = format!("{}.{}", module_path, leading);
                    if module_paths.contains(&candidate) {
                        let rest: String = path[1..].join(".");
                        return Some(format!("{}.{}", candidate, rest));
                    }
                }
                return Some(path.join("."));
            }
            _ => return None,
        }
    }
}

fn is_upper(s: &str) -> bool {
    s.chars().next().map(|c| c.is_ascii_uppercase()).unwrap_or(false)
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

    fn flatten(src: &str) -> Program {
        flatten_modules(parse(src)).expect("flatten")
    }

    fn fn_names(p: &Program) -> Vec<String> {
        p.items.iter().filter_map(|it| match &**it {
            Item::Fn(d) => Some(d.name.clone()),
            _ => None,
        }).collect()
    }

    #[test]
    fn module_qualifies_fn_names() {
        let p = flatten("defmodule M do; fn f(x), do: x + 1 end");
        assert_eq!(fn_names(&p), vec!["M.f"]);
    }

    #[test]
    fn ungrouped_fns_keep_bare_names() {
        let p = flatten("fn helper(x), do: x + 1");
        assert_eq!(fn_names(&p), vec!["helper"]);
    }

    #[test]
    fn sibling_call_in_module_rewrites() {
        let p = flatten(r#"
defmodule M do
  fn helper(x), do: x + 1
  fn use_helper(x), do: helper(x)
end
"#);
        let names = fn_names(&p);
        assert!(names.contains(&"M.helper".to_string()));
        assert!(names.contains(&"M.use_helper".to_string()));
        // Inspect the rewritten body of M.use_helper.
        let use_helper = p.items.iter().find_map(|it| match &**it {
            Item::Fn(d) if d.name == "M.use_helper" => Some(d),
            _ => None,
        }).unwrap();
        let body = &use_helper.clauses[0].body;
        match body {
            Expr::Call(callee, _) => match &**callee {
                Expr::Var(n) => assert_eq!(n, "M.helper"),
                other => panic!("expected Var('M.helper'), got {:?}", other),
            },
            other => panic!("expected Call, got {:?}", other),
        }
    }

    #[test]
    fn cross_module_call_rewrites() {
        let p = flatten(r#"
defmodule A do
  fn ping(), do: 1
end
defmodule B do
  fn caller(), do: A.ping()
end
"#);
        let caller = p.items.iter().find_map(|it| match &**it {
            Item::Fn(d) if d.name == "B.caller" => Some(d),
            _ => None,
        }).unwrap();
        let body = &caller.clauses[0].body;
        match body {
            Expr::Call(callee, _) => match &**callee {
                Expr::Var(n) => assert_eq!(n, "A.ping"),
                other => panic!("expected Var('A.ping'), got {:?}", other),
            },
            other => panic!("expected Call, got {:?}", other),
        }
    }

    #[test]
    fn local_param_does_not_qualify() {
        // `helper` is both a sibling fn name and a param name. The body
        // refers to the param, NOT the sibling.
        let p = flatten(r#"
defmodule M do
  fn helper(x), do: x
  fn shadow(helper), do: helper
end
"#);
        let shadow = p.items.iter().find_map(|it| match &**it {
            Item::Fn(d) if d.name == "M.shadow" => Some(d),
            _ => None,
        }).unwrap();
        let body = &shadow.clauses[0].body;
        match body {
            Expr::Var(n) => assert_eq!(n, "helper", "param shadow should preserve bare name"),
            other => panic!("expected Var('helper'), got {:?}", other),
        }
    }

    #[test]
    fn nested_module_qualifies_with_dotted_path() {
        let p = flatten(r#"
defmodule A do
  defmodule B do
    fn f(x), do: x + 1
  end
end
"#);
        assert_eq!(fn_names(&p), vec!["A.B.f"]);
    }

    #[test]
    fn nested_call_from_outside_rewrites() {
        let p = flatten(r#"
defmodule A do
  defmodule B do
    fn f(x), do: x
  end
end
fn main() do A.B.f(99) end
"#);
        let main_fn = p.items.iter().find_map(|it| match &**it {
            Item::Fn(d) if d.name == "main" => Some(d),
            _ => None,
        }).unwrap();
        let body = &main_fn.clauses[0].body;
        match body {
            Expr::Call(callee, _) => match &**callee {
                Expr::Var(n) => assert_eq!(n, "A.B.f"),
                other => panic!("expected Var('A.B.f'), got {:?}", other),
            },
            other => panic!("expected Call, got {:?}", other),
        }
    }

    #[test]
    fn outer_sibling_not_shadowed_by_inner_same_name() {
        // A.f and A.B.f coexist. From inside A's `caller`, bare `f(x)`
        // resolves to A.f, not A.B.f.
        let p = flatten(r#"
defmodule A do
  fn f(x), do: x
  fn caller(x), do: f(x)
  defmodule B do
    fn f(x), do: x + 100
  end
end
"#);
        let names = fn_names(&p);
        assert!(names.contains(&"A.f".to_string()));
        assert!(names.contains(&"A.B.f".to_string()));
        let caller = p.items.iter().find_map(|it| match &**it {
            Item::Fn(d) if d.name == "A.caller" => Some(d),
            _ => None,
        }).unwrap();
        let body = &caller.clauses[0].body;
        match body {
            Expr::Call(callee, _) => match &**callee {
                Expr::Var(n) => assert_eq!(n, "A.f"),
                other => panic!("expected Var('A.f'), got {:?}", other),
            },
            other => panic!("expected Call, got {:?}", other),
        }
    }
}
