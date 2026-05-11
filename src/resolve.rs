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
//!
//! Span policy (post-.20.2): rewrites preserve the original AST node's
//! span. Replacing `helper(x)` with `M.helper(x)` keeps the call's span
//! pointing at the bare-name source position — that's the right
//! diagnostic source for "this call resolves to …".

use crate::ast::*;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// REPL helper: rewrite cross-module `Mod.fn(args)` calls in a single
/// expression. No sibling-fn rewriting (the REPL has no enclosing
/// module).
pub fn rewrite_expr_top_level(e: &mut Spanned<Expr>) {
    let no_siblings: HashSet<String> = HashSet::new();
    let mut intro: HashSet<String> = HashSet::new();
    let no_paths: HashSet<String> = HashSet::new();
    let no_aliases: HashMap<String, String> = HashMap::new();
    let no_imports: HashMap<(String, usize), String> = HashMap::new();
    rewrite_expr(e, "", &no_siblings, &mut intro, &no_paths, &no_aliases, &no_imports);
}

pub fn flatten_modules(prog: Program) -> Result<Program, String> {
    let module_paths = collect_module_paths(&prog);
    let module_fns = collect_module_fns(&prog);
    let mut out: Vec<Rc<Item>> = Vec::new();
    let no_aliases: HashMap<String, String> = HashMap::new();
    let no_imports: HashMap<(String, usize), String> = HashMap::new();
    for item in &prog.items {
        match &**item {
            Item::Fn(def) => {
                let mut new_def = def.clone();
                let no_siblings: HashSet<String> = HashSet::new();
                for clause in &mut new_def.clauses {
                    let mut intro = pattern_intro(&clause.params);
                    rewrite_expr(&mut clause.body, "", &no_siblings, &mut intro,
                        &module_paths, &no_aliases, &no_imports);
                    if let Some(g) = &mut clause.guard {
                        rewrite_expr(g, "", &no_siblings, &mut intro,
                            &module_paths, &no_aliases, &no_imports);
                    }
                }
                out.push(Rc::new(Item::Fn(new_def)));
            }
            Item::Module(m) => flatten_module(m, "", &mut out, &module_paths, &module_fns)?,
            Item::Alias { .. } => return Err(
                "alias is only valid inside a defmodule body".into()
            ),
            Item::Import { .. } => return Err(
                "import is only valid inside a defmodule body".into()
            ),
            Item::MacroCall { name, name_span, args, parent_module: _, span } => {
                let no_siblings: HashSet<String> = HashSet::new();
                let mut new_args: Vec<Spanned<Expr>> = args.clone();
                for a in &mut new_args {
                    let mut intro: HashSet<String> = HashSet::new();
                    rewrite_expr(a, "", &no_siblings, &mut intro,
                        &module_paths, &no_aliases, &no_imports);
                }
                out.push(Rc::new(Item::MacroCall {
                    name: name.clone(),
                    name_span: *name_span,
                    args: new_args,
                    parent_module: None,
                    span: *span,
                }));
            }
        }
    }
    Ok(Program { items: out })
}

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

type ModuleFns = HashMap<String, HashSet<(String, usize)>>;

fn collect_module_fns(prog: &Program) -> ModuleFns {
    let mut out: ModuleFns = HashMap::new();
    for item in &prog.items {
        if let Item::Module(m) = &**item {
            collect_module_fns_recursive(m, "", &mut out);
        }
    }
    out
}

fn collect_module_fns_recursive(m: &ModuleDef, parent: &str, out: &mut ModuleFns) {
    let path = if parent.is_empty() { m.name.clone() } else { format!("{}.{}", parent, m.name) };
    out.entry(path.clone()).or_default();
    for item in &m.items {
        match &**item {
            Item::Fn(def) => {
                let arity = def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
                out.get_mut(&path).unwrap().insert((def.name.clone(), arity));
            }
            Item::Module(inner) => collect_module_fns_recursive(inner, &path, out),
            _ => {}
        }
    }
}

fn flatten_module(
    m: &ModuleDef,
    parent_path: &str,
    out: &mut Vec<Rc<Item>>,
    module_paths: &HashSet<String>,
    module_fns: &ModuleFns,
) -> Result<(), String> {
    let module_path = if parent_path.is_empty() {
        m.name.clone()
    } else {
        format!("{}.{}", parent_path, m.name)
    };
    let mut siblings: HashSet<String> = HashSet::new();
    let mut aliases: HashMap<String, String> = HashMap::new();
    let mut imports: HashMap<(String, usize), String> = HashMap::new();
    for item in &m.items {
        match &**item {
            Item::Fn(def) => { siblings.insert(def.name.clone()); }
            Item::Alias { full_path, as_name, .. } => {
                aliases.insert(as_name.clone(), full_path.join("."));
            }
            Item::Import { path, only, except, .. } => {
                let path_s = path.join(".");
                let target_fns = module_fns.get(&path_s).cloned().unwrap_or_default();
                let pairs: Vec<(String, usize)> = if let Some(allow) = only {
                    allow.clone()
                } else if let Some(deny) = except {
                    let deny_set: HashSet<(String, usize)> = deny.iter().cloned().collect();
                    target_fns.iter()
                        .filter(|p| !deny_set.contains(*p))
                        .cloned()
                        .collect()
                } else {
                    target_fns.iter().cloned().collect()
                };
                for (name, arity) in pairs {
                    imports.insert((name, arity), path_s.clone());
                }
            }
            Item::Module(_) | Item::MacroCall { .. } => {}
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
                    rewrite_expr(&mut clause.body, &module_path, &siblings, &mut intro,
                        module_paths, &aliases, &imports);
                    if let Some(g) = &mut clause.guard {
                        rewrite_expr(g, &module_path, &siblings, &mut intro,
                            module_paths, &aliases, &imports);
                    }
                }
                out.push(Rc::new(Item::Fn(new_def)));
            }
            Item::Module(inner) => {
                flatten_module(inner, &module_path, out, module_paths, module_fns)?;
            }
            Item::Alias { .. } | Item::Import { .. } => {}
            Item::MacroCall { name, name_span, args, parent_module: _, span } => {
                let mut new_args: Vec<Spanned<Expr>> = args.clone();
                for a in &mut new_args {
                    let mut intro: HashSet<String> = HashSet::new();
                    rewrite_expr(a, &module_path, &siblings, &mut intro,
                        module_paths, &aliases, &imports);
                }
                out.push(Rc::new(Item::MacroCall {
                    name: name.clone(),
                    name_span: *name_span,
                    args: new_args,
                    parent_module: Some(module_path.clone()),
                    span: *span,
                }));
            }
        }
    }
    Ok(())
}

fn pattern_intro(params: &[Spanned<Pattern>]) -> HashSet<String> {
    let mut s = HashSet::new();
    for p in params { collect_pattern_vars(&p.node, &mut s); }
    s
}

fn collect_pattern_vars(p: &Pattern, out: &mut HashSet<String>) {
    match p {
        Pattern::Var(n) => { out.insert(n.clone()); }
        Pattern::As(n, inner) => { out.insert(n.clone()); collect_pattern_vars(&inner.node, out); }
        Pattern::Tuple(xs) => for x in xs { collect_pattern_vars(&x.node, out); },
        Pattern::List(xs, tail) => {
            for x in xs { collect_pattern_vars(&x.node, out); }
            if let Some(t) = tail { collect_pattern_vars(&t.node, out); }
        }
        Pattern::Map(pairs) => for (_, v) in pairs { collect_pattern_vars(&v.node, out); },
        Pattern::Bitstring(fields) => for f in fields { collect_pattern_vars(&f.value.node, out); },
        _ => {}
    }
}

fn rewrite_expr(
    e: &mut Spanned<Expr>,
    module_path: &str,
    siblings: &HashSet<String>,
    intro: &mut HashSet<String>,
    module_paths: &HashSet<String>,
    aliases: &HashMap<String, String>,
    imports: &HashMap<(String, usize), String>,
) {
    match &mut e.node {
        Expr::Var(n) => {
            if siblings.contains(n) && !intro.contains(n) {
                *n = format!("{}.{}", module_path, n);
            }
        }
        Expr::Call(callee, args) => {
            if let Some(q) = qualify_callee(callee, intro, module_path, module_paths, aliases) {
                callee.node = Expr::Var(q);
            } else if let Expr::Var(n) = &callee.node {
                if !intro.contains(n) && !siblings.contains(n) {
                    if let Some(target) = imports.get(&(n.clone(), args.len())) {
                        callee.node = Expr::Var(format!("{}.{}", target, n));
                    }
                }
            }
            rewrite_expr(callee, module_path, siblings, intro, module_paths, aliases, imports);
            for a in args { rewrite_expr(a, module_path, siblings, intro, module_paths, aliases, imports); }
        }
        Expr::List(xs, tail) => {
            for x in xs { rewrite_expr(x, module_path, siblings, intro, module_paths, aliases, imports); }
            if let Some(t) = tail { rewrite_expr(t, module_path, siblings, intro, module_paths, aliases, imports); }
        }
        Expr::Tuple(xs) | Expr::VecLit(_, xs) | Expr::Block(xs) => {
            for x in xs { rewrite_expr(x, module_path, siblings, intro, module_paths, aliases, imports); }
        }
        Expr::Bitstring(fields) => for f in fields { rewrite_expr(&mut f.value, module_path, siblings, intro, module_paths, aliases, imports); },
        Expr::Map(pairs) => for (k, v) in pairs {
            rewrite_expr(k, module_path, siblings, intro, module_paths, aliases, imports);
            rewrite_expr(v, module_path, siblings, intro, module_paths, aliases, imports);
        },
        Expr::MapUpdate(m, pairs) => {
            rewrite_expr(m, module_path, siblings, intro, module_paths, aliases, imports);
            for (k, v) in pairs {
                rewrite_expr(k, module_path, siblings, intro, module_paths, aliases, imports);
                rewrite_expr(v, module_path, siblings, intro, module_paths, aliases, imports);
            }
        }
        Expr::Index(o, i) => {
            rewrite_expr(o, module_path, siblings, intro, module_paths, aliases, imports);
            rewrite_expr(i, module_path, siblings, intro, module_paths, aliases, imports);
        }
        Expr::Dot(o, _) => rewrite_expr(o, module_path, siblings, intro, module_paths, aliases, imports),
        Expr::BinOp(_, l, r) => {
            rewrite_expr(l, module_path, siblings, intro, module_paths, aliases, imports);
            rewrite_expr(r, module_path, siblings, intro, module_paths, aliases, imports);
        }
        Expr::UnOp(_, x) => rewrite_expr(x, module_path, siblings, intro, module_paths, aliases, imports),
        Expr::If(c, t, els) => {
            rewrite_expr(c, module_path, siblings, intro, module_paths, aliases, imports);
            rewrite_expr(t, module_path, siblings, intro, module_paths, aliases, imports);
            if let Some(e) = els { rewrite_expr(e, module_path, siblings, intro, module_paths, aliases, imports); }
        }
        Expr::Case(scr, arms) => {
            rewrite_expr(scr, module_path, siblings, intro, module_paths, aliases, imports);
            for arm in arms {
                let mut nested = intro.clone();
                collect_pattern_vars(&arm.pattern.node, &mut nested);
                if let Some(g) = &mut arm.guard { rewrite_expr(g, module_path, siblings, &mut nested, module_paths, aliases, imports); }
                rewrite_expr(&mut arm.body, module_path, siblings, &mut nested, module_paths, aliases, imports);
            }
        }
        Expr::Cond(pairs) => {
            for (c, b) in pairs {
                rewrite_expr(c, module_path, siblings, intro, module_paths, aliases, imports);
                rewrite_expr(b, module_path, siblings, intro, module_paths, aliases, imports);
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            let mut nested = intro.clone();
            for b in bindings {
                match b {
                    WithBinding::Match(p, e) => {
                        rewrite_expr(e, module_path, siblings, &mut nested, module_paths, aliases, imports);
                        collect_pattern_vars(&p.node, &mut nested);
                    }
                    WithBinding::Bare(e) => rewrite_expr(e, module_path, siblings, &mut nested, module_paths, aliases, imports),
                }
            }
            rewrite_expr(body, module_path, siblings, &mut nested, module_paths, aliases, imports);
            for arm in else_clauses {
                let mut a_intro = intro.clone();
                collect_pattern_vars(&arm.pattern.node, &mut a_intro);
                if let Some(g) = &mut arm.guard { rewrite_expr(g, module_path, siblings, &mut a_intro, module_paths, aliases, imports); }
                rewrite_expr(&mut arm.body, module_path, siblings, &mut a_intro, module_paths, aliases, imports);
            }
        }
        Expr::Match(pat, rhs) => {
            rewrite_expr(rhs, module_path, siblings, intro, module_paths, aliases, imports);
            collect_pattern_vars(&pat.node, intro);
        }
        Expr::Lambda(params, body) => {
            let mut nested = intro.clone();
            for p in params { collect_pattern_vars(&p.node, &mut nested); }
            rewrite_expr(body, module_path, siblings, &mut nested, module_paths, aliases, imports);
        }
        Expr::Quote(inner) => rewrite_expr(inner, module_path, siblings, intro, module_paths, aliases, imports),
        Expr::Unquote(inner) => rewrite_expr(inner, module_path, siblings, intro, module_paths, aliases, imports),
        Expr::Int(_) | Expr::Float(_) | Expr::Str(_) | Expr::Atom(_)
        | Expr::Bool(_) | Expr::Nil => {}
    }
}

fn qualify_callee(
    callee: &Spanned<Expr>,
    intro: &HashSet<String>,
    module_path: &str,
    module_paths: &HashSet<String>,
    aliases: &HashMap<String, String>,
) -> Option<String> {
    let mut path: Vec<String> = Vec::new();
    let mut cur = &callee.node;
    loop {
        match cur {
            Expr::Index(target, key) => {
                let member = match &key.node {
                    Expr::Atom(n) => n.clone(),
                    _ => return None,
                };
                path.push(member);
                cur = &target.node;
            }
            Expr::Dot(target, member) => {
                path.push(member.clone());
                cur = &target.node;
            }
            Expr::Var(m) if is_upper(m) && !intro.contains(m) => {
                if path.is_empty() { return None; }
                path.push(m.clone());
                path.reverse();
                let leading = &path[0];
                if let Some(full) = aliases.get(leading) {
                    let rest: String = path[1..].join(".");
                    return Some(if rest.is_empty() {
                        full.clone()
                    } else {
                        format!("{}.{}", full, rest)
                    });
                }
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

    fn callee_name(body: &Spanned<Expr>) -> &str {
        match &body.node {
            Expr::Call(callee, _) => match &callee.node {
                Expr::Var(n) => n.as_str(),
                other => panic!("expected Var callee, got {:?}", other),
            },
            other => panic!("expected Call, got {:?}", other),
        }
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
        let use_helper = p.items.iter().find_map(|it| match &**it {
            Item::Fn(d) if d.name == "M.use_helper" => Some(d),
            _ => None,
        }).unwrap();
        assert_eq!(callee_name(&use_helper.clauses[0].body), "M.helper");
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
        assert_eq!(callee_name(&caller.clauses[0].body), "A.ping");
    }

    #[test]
    fn local_param_does_not_qualify() {
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
        match &shadow.clauses[0].body.node {
            Expr::Var(n) => assert_eq!(n, "helper"),
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
        assert_eq!(callee_name(&main_fn.clauses[0].body), "A.B.f");
    }

    #[test]
    fn alias_inside_module_resolves() {
        let p = flatten(r#"
defmodule Long do
  defmodule Path do
    fn f(x), do: x
  end
end
defmodule User do
  alias Long.Path
  fn caller(), do: Path.f(7)
end
"#);
        let caller = p.items.iter().find_map(|it| match &**it {
            Item::Fn(d) if d.name == "User.caller" => Some(d),
            _ => None,
        }).unwrap();
        assert_eq!(callee_name(&caller.clauses[0].body), "Long.Path.f");
    }

    #[test]
    fn alias_with_as_renames() {
        let p = flatten(r#"
defmodule Long do
  defmodule Path do
    fn f(x), do: x
  end
end
defmodule User do
  alias Long.Path, as: P
  fn caller(), do: P.f(9)
end
"#);
        let caller = p.items.iter().find_map(|it| match &**it {
            Item::Fn(d) if d.name == "User.caller" => Some(d),
            _ => None,
        }).unwrap();
        assert_eq!(callee_name(&caller.clauses[0].body), "Long.Path.f");
    }

    #[test]
    fn import_unfiltered_pulls_all_names() {
        let p = flatten(r#"
defmodule Math do
  fn add(x, y), do: x + y
  fn mul(x, y), do: x * y
end
defmodule User do
  import Math
  fn run(x, y), do: add(x, y)
end
"#);
        let run = p.items.iter().find_map(|it| match &**it {
            Item::Fn(d) if d.name == "User.run" => Some(d),
            _ => None,
        }).unwrap();
        assert_eq!(callee_name(&run.clauses[0].body), "Math.add");
    }

    #[test]
    fn import_only_filters_names() {
        let p = flatten(r#"
defmodule Math do
  fn add(x, y), do: x + y
  fn mul(x, y), do: x * y
end
defmodule User do
  import Math, only: [add: 2]
  fn r1(x, y), do: add(x, y)
  fn r2(x, y), do: mul(x, y)
end
"#);
        let r1 = p.items.iter().find_map(|it| match &**it {
            Item::Fn(d) if d.name == "User.r1" => Some(d),
            _ => None,
        }).unwrap();
        assert_eq!(callee_name(&r1.clauses[0].body), "Math.add");
        let r2 = p.items.iter().find_map(|it| match &**it {
            Item::Fn(d) if d.name == "User.r2" => Some(d),
            _ => None,
        }).unwrap();
        assert_eq!(callee_name(&r2.clauses[0].body), "mul");
    }

    #[test]
    fn local_fn_shadows_import() {
        let p = flatten(r#"
defmodule Math do
  fn add(x, y), do: x + y
end
defmodule User do
  import Math
  fn add(x, y), do: x - y
  fn use_local(), do: add(10, 4)
end
"#);
        let use_local = p.items.iter().find_map(|it| match &**it {
            Item::Fn(d) if d.name == "User.use_local" => Some(d),
            _ => None,
        }).unwrap();
        assert_eq!(callee_name(&use_local.clauses[0].body), "User.add");
    }

    #[test]
    fn import_outside_module_errors() {
        let r = flatten_modules(parse(r#"
import Some.Mod
fn main(), do: nil
"#));
        assert!(r.is_err());
    }

    #[test]
    fn alias_outside_module_errors() {
        let r = flatten_modules(parse(r#"
alias Some.Mod
fn main(), do: nil
"#));
        assert!(r.is_err());
    }

    #[test]
    fn moduledoc_and_doc_parse() {
        let prog = parse(r#"
defmodule Greeter do
  @moduledoc "Greets people."

  @doc "Says hi."
  fn hi(name), do: name
end
"#);
        let m = prog.items.iter().find_map(|it| match &**it {
            Item::Module(m) => Some(m), _ => None,
        }).unwrap();
        assert_eq!(m.moduledoc.as_deref(), Some("Greets people."));
        let hi = m.items.iter().find_map(|it| match &**it {
            Item::Fn(d) if d.name == "hi" => Some(d), _ => None,
        }).unwrap();
        assert_eq!(hi.doc.as_deref(), Some("Says hi."));
    }

    #[test]
    fn unknown_attribute_errors() {
        let toks = crate::lexer::Lexer::new("@bogus \"x\"\nfn main(), do: nil")
            .tokenize().unwrap();
        let r = Parser::new(toks).parse_program();
        assert!(r.is_err());
    }

    #[test]
    fn moduledoc_at_top_level_errors() {
        let toks = crate::lexer::Lexer::new("@moduledoc \"x\"\nfn main(), do: nil")
            .tokenize().unwrap();
        let r = Parser::new(toks).parse_program();
        assert!(r.is_err());
    }

    #[test]
    fn doc_survives_flatten() {
        let p = flatten(r#"
defmodule M do
  @doc "doubles"
  fn d(x), do: x * 2
end
"#);
        let d = p.items.iter().find_map(|it| match &**it {
            Item::Fn(d) if d.name == "M.d" => Some(d),
            _ => None,
        }).unwrap();
        assert_eq!(d.doc.as_deref(), Some("doubles"));
    }

    #[test]
    fn outer_sibling_not_shadowed_by_inner_same_name() {
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
        assert_eq!(callee_name(&caller.clauses[0].body), "A.f");
    }
}
