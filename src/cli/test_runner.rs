//! fz-ul4.16.4 — `fz test <path>` subcommand.
//!
//! Auto-prepends a tiny prelude that defines the `test` macro:
//!
//!   defmacro test(name_atom, [do: body]) do
//!     {:fn_def, name_atom, body}
//!   end
//!
//! …so user-side test files can write
//!
//!   test(:test_addition) do
//!     assert(1 + 1 == 2)
//!   end
//!
//! After parse → resolve → expand, the `test(:test_addition) do ... end`
//! call splices in `fn test_addition() do ... end`. The runner discovers
//! every fn whose final segment starts with `test_`, calls it through
//! `ir_interp`, and reports results in an ExUnit-shaped summary.
//!
//! KNOWN LIMITATION (fz-ul4.16.5): item-macros inside a defmodule body
//! produce fns under bare names. So tests inside `defmodule MyTest do ...`
//! end up at top-level. Tests at top-level work fine.
//!
//! Asserts: `assert(cond)`, `assert(a == b)`, `refute(a == b)` are runtime
//! builtins surfaced through the IR interpreter. Each returns an assertion
//! error on failure; the runner catches the error.

use crate::ast::Item;
use crate::compiler::source::SourceMap;
use crate::compiler::{Compiler, World};
use crate::diag::render_one_to_string;
use crate::fz_ir::FnId;
use crate::ir_interp::run_test_fn;
use crate::measurements;
use crate::metadata;
use crate::modules::pipeline::CompileMode;
use crate::notify_fixture_execution_start;
use crate::parser::Parser;
use crate::parser::lexer::{Lexer, Tok, Token};
use crate::telemetry::{ConfiguredTelemetry, Event, Handler, Metadata, Telemetry};
use std::borrow::Cow;
use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::fs::read_to_string;
use std::path::Path;

const PRELUDE: &str = r#"
defmacro test(name_atom, [do: body]) do
  {:fn_def, name_atom, body}
end
"#;

#[derive(Debug)]
pub struct TestRunError(pub String);
impl Display for TestRunError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "fz test: {}", self.0)
    }
}
impl Error for TestRunError {}

/// Concatenate two token streams, dropping the prelude's trailing Eof so
/// the parser sees one stream. The user stream's Eof is kept as the real
/// terminator.
fn splice_token_streams(mut prelude: Vec<Token>, user: Vec<Token>) -> Vec<Token> {
    while matches!(prelude.last().map(|t| &t.tok), Some(Tok::Eof)) {
        prelude.pop();
    }
    prelude.extend(user);
    prelude
}

pub fn run(path: &Path) -> Result<(), TestRunError> {
    let user_src = read_to_string(path).map_err(|e| TestRunError(format!("reading {}: {}", path.display(), e)))?;
    let tel = build_console_telemetry();
    run_named_through(&tel, &user_src, &path.display().to_string())
}

#[cfg(test)]
pub fn run_str(user_src: &str) -> Result<(), TestRunError> {
    let tel = build_console_telemetry();
    run_named_through(&tel, user_src, "<input>")
}

/// Drive the test runner against a caller-supplied telemetry bus. Useful
/// when the caller already has a bus configured (e.g. for capture-based
/// assertions in tests, or for piping the event stream to a custom sink).
#[cfg(test)]
pub fn run_through(tel: &dyn Telemetry, src: &str) -> Result<(), TestRunError> {
    run_named_through(tel, src, "<input>")
}

fn build_console_telemetry() -> ConfiguredTelemetry {
    let tel = ConfiguredTelemetry::new();
    tel.attach(&["fz", "test"], Box::new(ConsoleTestHandler));
    tel
}

/// Default human-readable handler for `[fz, test, *]` events. Reproduces
/// the historical `fz test` output: header, per-test ok/FAIL lines,
/// summary count.
struct ConsoleTestHandler;

impl Handler for ConsoleTestHandler {
    fn handle(&self, ev: &Event<'_, '_, '_>) {
        use crate::telemetry::Value;
        match ev.name {
            n if n == ["fz", "test", "no_tests_found"] => {
                println!("No tests found (define `fn test_*()` or use `test :test_name do ... end`).");
            }
            n if n == ["fz", "test", "run_starting"] => {
                let count = match ev.measurements.get("count") {
                    Some(Value::U64(c)) => *c,
                    _ => 0,
                };
                let s = if count == 1 { "" } else { "s" };
                println!("Running {} test{}...", count, s);
                println!();
            }
            n if n == ["fz", "test", "passed"] => {
                let name = match ev.metadata.get("name") {
                    Some(Value::Str(s)) => s.clone(),
                    _ => return,
                };
                println!("  ok  {}", name);
            }
            n if n == ["fz", "test", "failed"] => {
                let name = match ev.metadata.get("name") {
                    Some(Value::Str(s)) => s.clone(),
                    _ => return,
                };
                let msg = match ev.metadata.get("message") {
                    Some(Value::Str(s)) => s.clone(),
                    _ => Cow::Borrowed(""),
                };
                println!("  FAIL  {}", name);
                println!("        {}", msg);
            }
            n if n == ["fz", "test", "summary"] => {
                let total = match ev.measurements.get("total") {
                    Some(Value::U64(c)) => *c,
                    _ => 0,
                };
                let failures = match ev.measurements.get("failures") {
                    Some(Value::U64(c)) => *c,
                    _ => 0,
                };
                let ts = if total == 1 { "" } else { "s" };
                let fs = if failures == 1 { "" } else { "s" };
                println!();
                println!("{} test{}, {} failure{}", total, ts, failures, fs);
            }
            _ => {}
        }
    }
}

fn run_named_through(tel: &dyn Telemetry, user_src: &str, user_name: &str) -> Result<(), TestRunError> {
    let mut compiler = Compiler::new();
    let mut world = World::new();
    // Lex prelude and user source separately into their own FileIds. Token
    // spans then point at the *real* offsets in their respective files, so
    // later stages render user-facing locations against the user's file
    // (not against a synthetic prelude+user concat). Eofs are filtered
    // between streams so the parser sees one continuous list.
    let mut sm = SourceMap::new();
    let prelude_id = sm.add_code("<prelude>", PRELUDE);
    let user_id = sm.add_code(user_name, user_src);
    // Lex/parse errors render through the shared renderer using the
    // SourceMap built above. Downstream stages still bubble up as
    // TestRunError strings — wiring spans through resolve / macros for
    // test output is a future ticket.
    let prelude_toks = Lexer::with_file_and_source_name(PRELUDE, prelude_id, "<test-prelude>")
        .tokenize(tel)
        .map_err(|e| TestRunError(render_one_to_string(&sm, &e.to_diagnostic())))?;
    let user_toks = Lexer::with_file_and_source_name(user_src, user_id, user_name)
        .tokenize(tel)
        .map_err(|e| TestRunError(render_one_to_string(&sm, &e.to_diagnostic())))?;
    let toks = splice_token_streams(prelude_toks, user_toks);
    let prog = Parser::new(toks)
        .parse_program(tel)
        .map_err(|e| TestRunError(render_one_to_string(&sm, &e.to_diagnostic())))?;
    let frontend = match compiler.compile_program(&mut world, prog, sm.clone(), tel) {
        Ok(frontend) => frontend,
        Err(err) => return Err(TestRunError(render_diagnostics(&err.sm, err.diagnostics.as_slice()))),
    };
    if frontend
        .diagnostics
        .as_slice()
        .iter()
        .any(|diagnostic| diagnostic.severity == crate::diag::diagnostic::Severity::Error)
    {
        return Err(TestRunError(render_diagnostics(
            &frontend.sm,
            frontend.diagnostics.as_slice(),
        )));
    }

    // Discover tests: post-expansion Item::Fn whose final segment starts
    // with "test_".
    let mut tests: Vec<String> = Vec::new();
    for item in &frontend._prog.items {
        if let Item::Fn(def) = &**item {
            if def.is_macro {
                continue;
            }
            let last = def.name.rsplit('.').next().unwrap_or(&def.name);
            if last.starts_with("test_") && def.clauses.iter().all(|c| c.params.is_empty()) {
                tests.push(def.name.clone());
            }
        }
    }
    tests.sort();

    if tests.is_empty() {
        tel.emit(&["fz", "test", "no_tests_found"]);
        return Ok(());
    }

    compiler
        .prepare_execution_graph_from_frontend(&mut world, frontend, tel, CompileMode::Normal)
        .map_err(|err| TestRunError(err.to_string()))?;
    // Map test name → FnId once.
    let test_ids: Vec<(String, FnId)> = tests
        .iter()
        .map(|name| {
            world
                .linked_module()
                .fn_by_name(name)
                .map(|f| (name.clone(), f.id))
                .ok_or_else(|| TestRunError(format!("test fn `{}` not in lowered module", name)))
        })
        .collect::<Result<_, _>>()?;

    let total = tests.len();
    let mut failed: Vec<(String, String)> = Vec::new();
    tel.execute(
        &["fz", "test", "run_starting"],
        &measurements! { count: total },
        &Metadata::new(),
    );
    notify_fixture_execution_start();
    for (name, fn_id) in &test_ids {
        // Each test runs in a fresh Process so heap/mailbox state from
        // one test doesn't leak into the next. ir_interp::run_main isn't
        // quite right (it expects a `main` fn); we call the test fn
        // directly through the IR interp on a temporary task.
        let module = world.linked_module().clone();
        let module_plan = world.linked_module_plan().clone();
        match run_test_fn(world.types(), tel, &module, &module_plan, *fn_id) {
            Ok(()) => {
                tel.event(&["fz", "test", "passed"], metadata! { name: name.clone() });
            }
            Err(msg) => {
                tel.event(
                    &["fz", "test", "failed"],
                    metadata! { name: name.clone(), message: msg.clone() },
                );
                failed.push((name.clone(), msg));
            }
        }
    }
    tel.execute(
        &["fz", "test", "summary"],
        &measurements! { total: total, failures: failed.len() },
        &Metadata::new(),
    );

    if !failed.is_empty() {
        return Err(TestRunError(format!("{} failing test(s)", failed.len())));
    }
    Ok(())
}

fn render_diagnostics(sm: &SourceMap, diagnostics: &[crate::diag::Diagnostic]) -> String {
    diagnostics
        .iter()
        .map(|diagnostic| render_one_to_string(sm, diagnostic))
        .collect::<String>()
}

#[cfg(test)]
#[path = "test_runner_test.rs"]
mod test_runner_test;
