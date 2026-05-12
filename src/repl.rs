//! fz-ul4.15 — read-eval-print loop. Reuses Interp directly.
//!
//! Each line is parsed first as a fn definition (top-level `fn`/`defmacro`),
//! falling back to an expression. Expressions evaluate in a persistent child
//! env of `interp.globals`, so `x = 42` on one line and `x + 1` on the next
//! both work — fz `=` is pattern-match-bind, which mutates the current frame.
//!
//! Multi-line input: if parsing fails with an EOF-shaped error (the parser
//! ran off the end mid-construct), the prompt switches to `... ` and keeps
//! buffering until the parser succeeds or returns a non-EOF error.
//!
//! `:quit` / `:q` / Ctrl-D exits.

use crate::ast::{Item, Program};
use crate::eval::Interp;
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::value::{Env, Value};
use std::io::{self, BufRead, Write};

pub fn run() -> io::Result<()> {
    let interp = Interp::new();
    // Persistent REPL frame for `x = 42`-style bindings. Closures created
    // in the REPL capture this frame via lookup-on-demand through Env.
    let repl_env = interp.globals.child();

    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut lines = stdin.lock().lines();

    println!("fz repl — :q to quit");
    let mut buf = String::new();
    loop {
        let prompt = if buf.is_empty() { "fz> " } else { "... " };
        write!(stdout, "{}", prompt)?;
        stdout.flush()?;

        let line = match lines.next() {
            Some(Ok(l)) => l,
            Some(Err(e)) => return Err(e),
            None => { println!(); break; }
        };
        let trimmed = line.trim();
        if buf.is_empty() && (trimmed == ":q" || trimmed == ":quit") { break; }
        if buf.is_empty() && trimmed.is_empty() { continue; }
        // `?name` — print @doc / @moduledoc for the given name. Mirrors
        // Elixir's `h fn`. Only fires at top level (empty buf) since it
        // isn't valid fz syntax.
        if buf.is_empty() && trimmed.starts_with('?') {
            let q = trimmed[1..].trim();
            println!("{}", lookup_doc(&interp, q));
            continue;
        }

        if !buf.is_empty() { buf.push('\n'); }
        buf.push_str(&line);

        match try_eval(&buf, &interp, &repl_env) {
            Outcome::Ok => buf.clear(),
            Outcome::Incomplete => { /* keep buffering */ }
            Outcome::Err(msg) => {
                eprintln!("{}", msg);
                buf.clear();
            }
        }
    }
    Ok(())
}

enum Outcome {
    Ok,
    Incomplete,
    Err(String),
}

fn try_eval(src: &str, interp: &Interp, env: &Env) -> Outcome {
    // Lex once. Lex errors are real errors (no incomplete-lex story for now).
    let toks = match Lexer::new(src).tokenize() {
        Ok(t) => t,
        Err(e) => return Outcome::Err(format!("{}", e)),
    };

    // Try as a fn definition (top-level). If the first non-newline token isn't
    // `fn` or `defmacro`, the program-parse will fail immediately; we then try
    // expression parsing.
    let starts_with_fn = toks.iter()
        .map(|t| &t.tok)
        .find(|t| !matches!(t, crate::lexer::Tok::Newline | crate::lexer::Tok::Semi))
        .map(|t| matches!(t,
            crate::lexer::Tok::Fn
            | crate::lexer::Tok::Defmacro
            | crate::lexer::Tok::Defmodule))
        .unwrap_or(false);

    if starts_with_fn {
        let mut p = Parser::new(toks);
        match p.parse_program() {
            Ok(prog) => {
                let mut prog = match crate::resolve::flatten_modules(prog) {
                    Ok(p) => p,
                    Err(e) => return Outcome::Err(format!("module: {}", e)),
                };
                for (path, doc) in &prog.module_docs {
                    interp.module_docs.borrow_mut().insert(path.clone(), doc.clone());
                }
                // Two-phase: load macros first (so they're callable during
                // expansion), expand fn bodies, then load the expanded fns.
                // Loading macros early also accumulates macro_names across
                // REPL batches.
                if let Err(e) = load_items_filtered(interp, &prog, /*macros=*/ true) {
                    return Outcome::Err(format!("load macros: {}", e));
                }
                let live = interp.macro_names.borrow().clone();
                if let Err(e) = crate::macros::expand_with(&mut prog, interp, &live) {
                    return Outcome::Err(format!("macro: {}", e));
                }
                if let Err(e) = load_items_filtered(interp, &prog, /*macros=*/ false) {
                    return Outcome::Err(format!("load fns: {}", e));
                }
                return Outcome::Ok;
            }
            Err(e) => {
                if is_incomplete(&e) { return Outcome::Incomplete; }
                return Outcome::Err(format!("{}", e));
            }
        }
    }

    let mut p = Parser::new(toks);
    match p.parse_expr_eof() {
        Ok(mut e) => {
            crate::resolve::rewrite_expr_top_level(&mut e);
            let live = interp.macro_names.borrow().clone();
            if let Err(msg) = crate::macros::expand_expr(&mut e, interp, &live, 0) {
                return Outcome::Err(format!("macro: {}", msg));
            }
            match interp.eval(&e, env) {
                Ok(Value::Nil) => Outcome::Ok,
                Ok(v) => { println!("{}", v); Outcome::Ok }
                Err(msg) => Outcome::Err(msg),
            }
        }
        Err(e) => {
            if is_incomplete(&e) { Outcome::Incomplete }
            else { Outcome::Err(format!("{}", e)) }
        }
    }
}

/// `which == true` loads only macros; `which == false` loads only non-macros.
/// Splitting the two phases lets the REPL register macros before running
/// expansion on fn bodies that may call them.
fn load_items_filtered(interp: &Interp, prog: &Program, macros_only: bool) -> Result<(), String> {
    use std::rc::Rc;
    for item in &prog.items {
        match &**item {
            Item::Module(_) | Item::Alias { .. } | Item::Import { .. } | Item::MacroCall { .. } => continue, // flattened away upstream
            Item::Fn(def) => {
                if macros_only != def.is_macro { continue; }
                if def.is_macro {
                    interp.macro_names.borrow_mut().insert(def.name.clone());
                    interp.macro_def_spans.borrow_mut().insert(def.name.clone(), def.span);
                }
                // If a closure already exists under this name *and* the new
                // clauses match arity, append. Otherwise replace. Matches
                // user expectation: typing several `fn foo(...)` lines in
                // sequence builds up a multi-clause fn.
                let existing = interp.globals.lookup(&def.name);
                let mut clauses = def.clauses.clone();
                let mut doc = def.doc().map(String::from);
                let mut spec_text = crate::eval::format_spec_text(def, prog);
                if let Some(Value::Closure(c)) = existing {
                    let same_arity = c.clauses.first().map(|cl| cl.params.len())
                        == clauses.first().map(|cl| cl.params.len());
                    if same_arity && c.name.as_deref() == Some(def.name.as_str()) {
                        let mut combined = c.clauses.clone();
                        combined.append(&mut clauses);
                        clauses = combined;
                        // Preserve prior doc / spec_text if the new def didn't carry one.
                        if doc.is_none() { doc = c.doc.clone(); }
                        if spec_text.is_none() { spec_text = c.spec_text.clone(); }
                    }
                }
                let closure = Value::Closure(Rc::new(crate::value::Closure {
                    name: Some(def.name.clone()),
                    clauses,
                    env: interp.globals.clone(),
                    doc,
                    spec_text,
                }));
                interp.globals.bind(&def.name, closure);
            }
        }
    }
    Ok(())
}

/// Resolve a `?<name>` REPL query against loaded fns and modules. Tries
/// fns first (so `?M.add` finds the closure), then falls back to a
/// moduledoc lookup (so `?M` finds the module).
///
/// fz-ul4.31.6 — renders `@spec` declaration alongside the `@doc` text
/// when both are present.
fn lookup_doc(interp: &Interp, name: &str) -> String {
    if name.is_empty() {
        return "usage: ?<fn-or-module-name>".to_string();
    }
    if let Some(Value::Closure(c)) = interp.globals.lookup(name) {
        let mut out = String::new();
        if let Some(s) = &c.spec_text {
            out.push_str("@spec: ");
            out.push_str(s);
        }
        if let Some(d) = &c.doc {
            if !out.is_empty() { out.push('\n'); }
            out.push_str("@doc:  ");
            out.push_str(d);
        }
        if out.is_empty() {
            return format!("{}: no documentation", name);
        }
        return out;
    }
    if let Some(d) = interp.module_docs.borrow().get(name) {
        return d.clone();
    }
    format!("{}: not found", name)
}

/// Heuristic: did the parser run off the end mid-construct? Those errors all
/// have the form "expected X, got Eof" or "got Tok::Eof". Real syntax errors
/// have a non-Eof token in the message.
fn is_incomplete(e: &crate::parser::ParseError) -> bool {
    e.msg.contains("Eof")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn load_program_test(interp: &Interp, prog: &Program) -> Result<(), String> {
        load_items_filtered(interp, prog, false)?;
        load_items_filtered(interp, prog, true)?;
        Ok(())
    }

    /// Drive the same parse path as the REPL but capture eval results in a
    /// vec rather than printing.
    fn drive(lines: &[&str]) -> Vec<Result<Value, String>> {
        let interp = Interp::new();
        let env = interp.globals.child();
        let mut buf = String::new();
        let mut out: Vec<Result<Value, String>> = Vec::new();
        for line in lines {
            if !buf.is_empty() { buf.push('\n'); }
            buf.push_str(line);

            let toks = match Lexer::new(&buf).tokenize() {
                Ok(t) => t,
                Err(e) => { out.push(Err(format!("{}", e))); buf.clear(); continue; }
            };
            let starts_with_fn = toks.iter().map(|t| &t.tok)
                .find(|t| !matches!(t, crate::lexer::Tok::Newline | crate::lexer::Tok::Semi))
                .map(|t| matches!(t, crate::lexer::Tok::Fn | crate::lexer::Tok::Defmacro))
                .unwrap_or(false);

            if starts_with_fn {
                let mut p = Parser::new(toks);
                match p.parse_program() {
                    Ok(prog) => {
                        load_program_test(&interp, &prog).unwrap();
                        out.push(Ok(Value::Nil));
                        buf.clear();
                    }
                    Err(e) if is_incomplete(&e) => {} // keep buffering
                    Err(e) => { out.push(Err(format!("{}", e))); buf.clear(); }
                }
                continue;
            }
            let mut p = Parser::new(toks);
            match p.parse_expr_eof() {
                Ok(e) => {
                    out.push(interp.eval(&e, &env));
                    buf.clear();
                }
                Err(e) if is_incomplete(&e) => {}
                Err(e) => { out.push(Err(format!("{}", e))); buf.clear(); }
            }
        }
        out
    }

    #[test]
    fn evaluates_simple_expression() {
        let r = drive(&["1 + 2"]);
        assert_eq!(r.len(), 1);
        assert!(matches!(r[0], Ok(Value::Int(3))));
    }

    #[test]
    fn binds_variable_across_inputs() {
        let r = drive(&["x = 7", "x + 35"]);
        assert_eq!(r.len(), 2);
        assert!(matches!(r[1], Ok(Value::Int(42))));
    }

    #[test]
    fn appends_clauses_to_existing_fn() {
        let r = drive(&[
            "fn fact(0), do: 1",
            "fn fact(n), do: n * fact(n - 1)",
            "fact(6)",
        ]);
        assert!(matches!(r[2], Ok(Value::Int(720))),
            "expected 720, got {:?}", r[2]);
    }

    #[test]
    fn buffers_multiline_do_end() {
        let r = drive(&[
            "fn double_plus(x) do",
            "  y = x + 1",
            "  y * 2",
            "end",
            "double_plus(20)",
        ]);
        // The first 4 lines are one buffered input; only line 4 ("end")
        // produces a load result. drive() pushes Ok(Nil) on fn load.
        let last = r.last().unwrap();
        assert!(matches!(last, Ok(Value::Int(42))), "got {:?}", last);
    }

    /// Drive a full program (lex → parse → flatten → load) and return the
    /// interp so doc-lookup tests can inspect post-load state. Mirrors what
    /// the REPL does for an item-level input, but in one shot.
    fn load(src: &str) -> Interp {
        let interp = Interp::new();
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let prog = crate::resolve::flatten_modules(prog).expect("resolve");
        for (path, doc) in &prog.module_docs {
            interp.module_docs.borrow_mut().insert(path.clone(), doc.clone());
        }
        load_program_test(&interp, &prog).expect("load");
        interp
    }

    #[test]
    fn doc_query_finds_module_fn_doc() {
        let interp = load(r#"
defmodule M do
  @doc "adds two"
  fn add(a, b), do: a + b
end
"#);
        assert_eq!(lookup_doc(&interp, "M.add"), "@doc:  adds two");
    }

    #[test]
    fn doc_query_finds_moduledoc() {
        let interp = load(r#"
defmodule M do
  @moduledoc "the M module"
  fn add(a, b), do: a + b
end
"#);
        assert_eq!(lookup_doc(&interp, "M"), "the M module");
    }

    #[test]
    fn doc_query_surfaces_spec_when_declared() {
        // .31.6 — `?<name>` renders @spec alongside @doc when both are
        // declared.
        let interp = load(r#"
defmodule M do
  @doc "adds one"
  @spec add1(integer) :: integer
  fn add1(n), do: n + 1
end
"#);
        let out = lookup_doc(&interp, "M.add1");
        assert!(out.contains("@spec"), "should render @spec line; got: {}", out);
        assert!(out.contains("@doc"), "should render @doc line; got: {}", out);
        // Descr Display renders integer as `int` (the lattice's name).
        assert!(out.contains("(int) -> int"),
            "should render declared Descrs; got: {}", out);
    }

    #[test]
    fn doc_query_surfaces_spec_without_doc() {
        // .31.6 — @spec alone still surfaces in `?<name>`.
        let interp = load(r#"
defmodule M do
  @spec add1(integer) :: integer
  fn add1(n), do: n + 1
end
"#);
        let out = lookup_doc(&interp, "M.add1");
        assert!(out.contains("@spec"), "should render @spec line; got: {}", out);
        assert!(!out.contains("no documentation"),
            "@spec alone counts as documentation; got: {}", out);
    }

    #[test]
    fn doc_query_missing_doc_reports_so() {
        let interp = load("fn plain(x), do: x");
        assert_eq!(lookup_doc(&interp, "plain"), "plain: no documentation");
    }

    #[test]
    fn doc_query_unknown_name_reports_not_found() {
        let interp = load("fn plain(x), do: x");
        assert_eq!(lookup_doc(&interp, "nope"), "nope: not found");
    }

    #[test]
    fn doc_query_empty_shows_usage() {
        let interp = Interp::new();
        assert!(lookup_doc(&interp, "").starts_with("usage:"));
    }

    #[test]
    fn redefines_fn_with_different_arity() {
        let r = drive(&[
            "fn f(x), do: x + 1",
            "fn f(x, y), do: x + y",
            "f(10, 20)",
        ]);
        // Different arity → replace, not append. f/2 should resolve.
        assert!(matches!(r[2], Ok(Value::Int(30))), "got {:?}", r[2]);
    }
}
