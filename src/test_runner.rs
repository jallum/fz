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
use crate::eval::Interp;
use crate::lexer::Lexer;
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

pub fn run(path: &Path) -> Result<(), TestRunError> {
    let user_src = std::fs::read_to_string(path)
        .map_err(|e| TestRunError(format!("reading {}: {}", path.display(), e)))?;
    run_str(&user_src)
}

pub fn run_str(user_src: &str) -> Result<(), TestRunError> {
    let combined = format!("{}\n{}", PRELUDE, user_src);
    let toks = Lexer::new(&combined)
        .tokenize().map_err(|e| TestRunError(format!("{}", e)))?;
    let prog = Parser::new(toks)
        .parse_program().map_err(|e| TestRunError(format!("{}", e)))?;
    let prog = flatten_modules(prog)
        .map_err(|e| TestRunError(format!("module: {}", e)))?;
    let mut prog = prog;
    expand_program(&mut prog)
        .map_err(|e| TestRunError(format!("macro: {}", e)))?;

    // Discover tests: post-expansion Item::Fn whose final segment starts
    // with "test_".
    let mut tests: Vec<String> = Vec::new();
    for item in &prog.items {
        if let Item::Fn(def) = &**item {
            if def.is_macro { continue; }
            let last = def.name.rsplit('.').next().unwrap_or(&def.name);
            if last.starts_with("test_") && def.clauses.iter().all(|c| c.params.is_empty()) {
                tests.push(def.name.clone());
            }
        }
    }
    tests.sort();

    if tests.is_empty() {
        println!("No tests found (define `fn test_*()` or use `test :test_name do ... end`).");
        return Ok(());
    }

    let interp = Interp::new();
    interp.load_program(&prog)
        .map_err(|e| TestRunError(format!("load: {}", e)))?;

    let total = tests.len();
    let mut failed: Vec<(String, String)> = Vec::new();
    println!("Running {} test{}...", total, if total == 1 { "" } else { "s" });
    println!();
    for name in &tests {
        match interp.call_named(name, vec![]) {
            Ok(_) => println!("  ok  {}", name),
            Err(msg) => {
                println!("  FAIL  {}", name);
                println!("        {}", msg);
                failed.push((name.clone(), msg));
            }
        }
    }
    println!();
    println!("{} test{}, {} failure{}",
        total, if total == 1 { "" } else { "s" },
        failed.len(), if failed.len() == 1 { "" } else { "s" });

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
}
