//! fz-ul4.16.4 — `fz test <path>` subcommand.
//!
//! Auto-prepends a tiny prelude that defines the `test` macro:
//!
//!   defmacro test(name_atom, body) do
//!     {:fn_def, name_atom, body}
//!   end
//!
//! …so user-side test files can write
//!
//!   test(:test_addition) do
//!     assert_eq(1 + 1, 2)
//!   end
//!
//! After parse → resolve → expand, the `test(:test_addition) do ... end`
//! call splices in `fn test_addition() do ... end`. The runner discovers
//! every fn whose final segment starts with `test_`, calls it via the
//! interpreter, and reports results in an ExUnit-shaped summary.
//!
//! KNOWN LIMITATION (fz-ul4.16.5): item-macros inside a defmodule body
//! produce fns under bare names. So tests inside `defmodule MyTest do ...`
//! end up at top-level. Tests at top-level work fine.
//!
//! Asserts: `assert(cond)`, `assert_eq(a, b)`, `assert_neq(a, b)` are
//! interp builtins (eval.rs). Each returns `Err("assertion failed: ...")`
//! on failure; the runner catches the error.

use crate::ast::Item;
use crate::diag::SourceMap;
use crate::lexer::{Lexer, Tok, Token};
use crate::macros::expand_program;
use crate::parser::Parser;
use crate::resolve::flatten_modules;
use std::path::Path;

const PRELUDE: &str = r#"
defmacro test(name_atom, body) do
  {:fn_def, name_atom, body}
end
"#;

#[derive(Debug)]
pub struct TestRunError(pub String);
impl std::fmt::Display for TestRunError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fz test: {}", self.0)
    }
}
impl std::error::Error for TestRunError {}

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
    let user_src = std::fs::read_to_string(path)
        .map_err(|e| TestRunError(format!("reading {}: {}", path.display(), e)))?;
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
#[allow(dead_code)]
pub fn run_through(tel: &dyn crate::telemetry::Telemetry, src: &str) -> Result<(), TestRunError> {
    run_named_through(tel, src, "<input>")
}

fn build_console_telemetry() -> crate::telemetry::ConfiguredTelemetry {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    tel.attach(&["fz", "test"], Box::new(ConsoleTestHandler));
    tel
}

/// Default human-readable handler for `[fz, test, *]` events. Reproduces
/// the historical `fz test` output: header, per-test ok/FAIL lines,
/// summary count.
struct ConsoleTestHandler;

impl crate::telemetry::Handler for ConsoleTestHandler {
    fn handle(&self, ev: &crate::telemetry::Event<'_>) {
        use crate::telemetry::Value;
        match ev.name {
            n if n == ["fz", "test", "no_tests_found"] => {
                println!(
                    "No tests found (define `fn test_*()` or use `test :test_name do ... end`)."
                );
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
                    _ => std::borrow::Cow::Borrowed(""),
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

fn run_named_through(
    tel: &dyn crate::telemetry::Telemetry,
    user_src: &str,
    user_name: &str,
) -> Result<(), TestRunError> {
    let mut t = crate::types::ConcreteTypes;
    // Lex prelude and user source separately into their own FileIds. Token
    // spans then point at the *real* offsets in their respective files, so
    // later stages render user-facing locations against the user's file
    // (not against a synthetic prelude+user concat). Eofs are filtered
    // between streams so the parser sees one continuous list.
    let mut sm = SourceMap::new();
    let prelude_id = sm.add_file("<prelude>", PRELUDE);
    let user_id = sm.add_file(user_name, user_src);
    // Lex/parse errors render through the shared renderer using the
    // SourceMap built above. Downstream stages still bubble up as
    // TestRunError strings — wiring spans through resolve / macros for
    // test output is a future ticket.
    let prelude_toks = Lexer::with_file(PRELUDE, prelude_id)
        .tokenize()
        .map_err(|e| TestRunError(crate::diag::render_one_to_string(&sm, &e.to_diagnostic())))?;
    let user_toks = Lexer::with_file(user_src, user_id)
        .tokenize()
        .map_err(|e| TestRunError(crate::diag::render_one_to_string(&sm, &e.to_diagnostic())))?;
    let toks = splice_token_streams(prelude_toks, user_toks);
    let prog = Parser::new(toks)
        .parse_program()
        .map_err(|e| TestRunError(crate::diag::render_one_to_string(&sm, &e.to_diagnostic())))?;
    let prog = flatten_modules(&mut t, prog)
        .map_err(|e| TestRunError(crate::diag::render_one_to_string(&sm, &e.to_diagnostic())))?;
    let mut prog = prog;
    expand_program(&mut prog)
        .map_err(|e| TestRunError(crate::diag::render_one_to_string(&sm, &e.to_diagnostic())))?;

    // Discover tests: post-expansion Item::Fn whose final segment starts
    // with "test_".
    let mut tests: Vec<String> = Vec::new();
    for item in &prog.items {
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
        tel.execute(
            &["fz", "test", "no_tests_found"],
            &crate::telemetry::Measurements::new(),
            &crate::telemetry::Metadata::new(),
        );
        return Ok(());
    }

    // Lower to fz-IR once; each test fn dispatches via ir_interp::run_fn.
    // This is the fz-ul4.23.5.10 migration: runtime execution leaves the
    // AST evaluator (eval::Interp, which stays only for macro expansion
    // above) and runs on the same IR interpreter the fixture matrix uses.
    let module = crate::ir_lower::lower_program(&mut t, &prog)
        .map_err(|e| TestRunError(crate::diag::render_one_to_string(&sm, &e.to_diagnostic())))?;
    // Map test name → FnId once.
    let test_ids: Vec<(String, crate::fz_ir::FnId)> = tests
        .iter()
        .map(|name| {
            module
                .fn_by_name(name)
                .map(|f| (name.clone(), f.id))
                .ok_or_else(|| TestRunError(format!("test fn `{}` not in lowered module", name)))
        })
        .collect::<Result<_, _>>()?;

    let total = tests.len();
    let mut failed: Vec<(String, String)> = Vec::new();
    tel.execute(
        &["fz", "test", "run_starting"],
        &crate::measurements! { count: total },
        &crate::telemetry::Metadata::new(),
    );
    for (name, fn_id) in &test_ids {
        // Each test runs in a fresh Process so heap/mailbox state from
        // one test doesn't leak into the next. ir_interp::run_main isn't
        // quite right (it expects a `main` fn); we call the test fn
        // directly through the IR interp on a temporary task.
        match crate::ir_interp::run_test_fn(&module, *fn_id) {
            Ok(()) => {
                tel.execute(
                    &["fz", "test", "passed"],
                    &crate::telemetry::Measurements::new(),
                    &crate::metadata! { name: name.clone() },
                );
            }
            Err(msg) => {
                tel.execute(
                    &["fz", "test", "failed"],
                    &crate::telemetry::Measurements::new(),
                    &crate::metadata! { name: name.clone(), message: msg.clone() },
                );
                failed.push((name.clone(), msg));
            }
        }
    }
    tel.execute(
        &["fz", "test", "summary"],
        &crate::measurements! { total: total, failures: failed.len() },
        &crate::telemetry::Metadata::new(),
    );

    if !failed.is_empty() {
        return Err(TestRunError(format!("{} failing test(s)", failed.len())));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn passing_test_runs_clean() {
        let src = r#"
test(:test_one) do
  assert_eq(1 + 1, 2)
end
"#;
        run_str(src).expect("test should pass");
    }

    #[test]
    fn failing_test_returns_err() {
        let src = r#"
test(:test_bad) do
  assert_eq(1 + 1, 3)
end
"#;
        let r = run_str(src);
        assert!(r.is_err(), "expected failure, got {:?}", r);
    }

    #[test]
    fn multiple_tests_some_fail() {
        let src = r#"
test(:test_a) do
  assert(true)
end
test(:test_b) do
  assert_eq(:x, :x)
end
test(:test_c) do
  assert_eq(1, 2)
end
"#;
        let r = run_str(src);
        assert!(r.is_err(), "expected at least one failure");
    }

    #[test]
    fn convention_style_test_fn_also_discovered() {
        // Skipping the macro: a hand-written `fn test_*() do ... end` is
        // also picked up.
        let src = r#"
fn test_plain() do
  assert(true)
end
"#;
        run_str(src).expect("test should pass");
    }

    #[test]
    fn no_tests_is_a_noop() {
        let src = "fn helper(x), do: x + 1";
        run_str(src).expect("no tests, no error");
    }

    // -- fz-ndf.10 telemetry --

    #[test]
    fn telemetry_capture_observes_passing_run() {
        use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

        let tel = ConfiguredTelemetry::new();
        let cap = Capture::new();
        tel.attach(&[], cap.handler());

        let src = r#"
test(:test_one) do
  assert_eq(1 + 1, 2)
end
test(:test_two) do
  assert_eq(:x, :x)
end
"#;
        run_through(&tel, src).expect("tests should pass");

        assert_eq!(cap.count(&["fz", "test", "run_starting"]), 1);
        assert_eq!(cap.count(&["fz", "test", "passed"]), 2);
        assert_eq!(cap.count(&["fz", "test", "failed"]), 0);
        let summary = cap.last(&["fz", "test", "summary"]).unwrap();
        assert!(matches!(
            summary.measurements.get("total"),
            Some(Value::U64(2))
        ));
        assert!(matches!(
            summary.measurements.get("failures"),
            Some(Value::U64(0))
        ));
    }

    #[test]
    fn telemetry_capture_observes_failing_test() {
        use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

        let tel = ConfiguredTelemetry::new();
        let cap = Capture::new();
        tel.attach(&[], cap.handler());

        let src = r#"
test(:test_ok) do
  assert(true)
end
test(:test_bad) do
  assert_eq(1, 2)
end
"#;
        let _ = run_through(&tel, src);
        assert_eq!(cap.count(&["fz", "test", "passed"]), 1);
        assert_eq!(cap.count(&["fz", "test", "failed"]), 1);
        let failure = cap.last(&["fz", "test", "failed"]).unwrap();
        assert!(matches!(failure.metadata.get("name"), Some(Value::Str(_))));
        assert!(matches!(
            failure.metadata.get("message"),
            Some(Value::Str(_))
        ));
    }

    #[test]
    fn telemetry_capture_observes_no_tests_found() {
        use crate::telemetry::{Capture, ConfiguredTelemetry};
        let tel = ConfiguredTelemetry::new();
        let cap = Capture::new();
        tel.attach(&[], cap.handler());
        run_through(&tel, "fn helper(x), do: x + 1").expect("no tests");
        assert_eq!(cap.count(&["fz", "test", "no_tests_found"]), 1);
        assert_eq!(cap.count(&["fz", "test", "summary"]), 0);
    }

}
