#[cfg(test)]
mod discover_tests_test {
    use super::super::discover_tests;
    use crate::telemetry::ConfiguredTelemetry;

    #[test]
    fn non_test_shaped_calls_are_skipped_not_discovered() {
        // `test(:t, 42)` (second arg is not a `do`-keyword list) and
        // `test("name") do ... end` (non-atom name) are not the `test` macro's
        // shape, so discovery skips them instead of recording a test that
        // would later blow up opaquely inside macro expansion. A well-formed
        // `test(:ok) do ... end` in the same file is still discovered.
        let tel = ConfiguredTelemetry::new();
        let source = "\
test(:t_two_args, 42)

test(\"not_an_atom\") do
  assert(true)
end

test(:ok) do
  assert(true)
end
";
        let tests = discover_tests("mixed.fz", source, &tel).expect("discover mixed tests");
        let names: Vec<String> = tests.iter().map(|test| test.display_name()).collect();
        assert_eq!(names, vec!["ok".to_string()]);
    }

    #[test]
    fn top_level_tests_are_discovered_unqualified_and_sorted_by_name() {
        // `fz2 test`'s discovery pre-parse finds every top-level `test(:name)
        // do ... end` item without expanding the `test` macro or running any
        // semantic compilation, and reports them in display-name order.
        let tel = ConfiguredTelemetry::new();
        let source = "\
test(:test_truthiness) do
  assert(true)
end

test(:test_addition) do
  assert(1 + 1 == 2)
end
";
        let tests = discover_tests("top_level.fz", source, &tel).expect("discover top-level tests");
        let names: Vec<String> = tests.iter().map(|test| test.display_name()).collect();
        assert_eq!(names, vec!["test_addition".to_string(), "test_truthiness".to_string()]);
        assert!(tests.iter().all(|test| test.module_path.is_empty()));
    }

    #[test]
    fn tests_nested_in_defmodule_are_module_qualified() {
        // A `test(...)` nested inside a `defmodule` is discovered too, and its
        // display name and `submit_root` module argument are qualified by the
        // enclosing module's dotted alias -- the same policy `run-test-root`
        // uses to submit the expanded fn as a root.
        let tel = ConfiguredTelemetry::new();
        let source = "\
defmodule MathTest do
  test(:test_arithmetic) do
    assert(1 + 1 == 2)
  end
end

test(:test_top_level) do
  assert(true)
end
";
        let tests = discover_tests("nested.fz", source, &tel).expect("discover nested tests");
        let names: Vec<String> = tests.iter().map(|test| test.display_name()).collect();
        assert_eq!(
            names,
            vec!["MathTest.test_arithmetic".to_string(), "test_top_level".to_string()]
        );
        let math_test = tests
            .iter()
            .find(|test| test.name == "test_arithmetic")
            .expect("MathTest.test_arithmetic discovered");
        assert_eq!(math_test.module_path, vec!["MathTest".to_string()]);
        assert_eq!(math_test.module_arg(), "MathTest");
    }
}

#[cfg(test)]
mod test_prelude_span_test {
    use super::super::{ScopeForm, TEST_MACRO_PRELUDE_NAME, TEST_MACRO_PRELUDE_SOURCE};
    use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
    use crate::telemetry::ConfiguredTelemetry;

    #[test]
    fn user_test_source_keeps_its_true_on_disk_span_offsets() {
        // The `test` item macro is supplied as a scoped prelude (its own
        // SourceOwner), never spliced into the user's source, so a node parsed from
        // the user's file carries its real byte offset. Under a textual prepend
        // the user buffer would be shifted forward by the prelude's length and
        // every span would be off by that many bytes -- this asserts the true
        // offset, so it fails against the concatenated-buffer approach.
        let tel = ConfiguredTelemetry::new();
        let mut compiler = Compiler2::new(tel);
        compiler.submit_scoped_prelude(CodeSubmission {
            name: Some(TEST_MACRO_PRELUDE_NAME.to_string()),
            text: TEST_MACRO_PRELUDE_SOURCE.to_string(),
        });
        let user_text = "def helper(x), do: x\n\ntest(:my_test) do\n  assert(helper(1) == 1)\nend\n".to_string();
        let user_code = compiler.submit_code(CodeSubmission {
            name: Some("user_test.fz".to_string()),
            text: user_text.clone(),
        });
        compiler.submit_root(RootSubmission {
            module_name: None,
            name: "my_test".to_string(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        let _ = compiler.drive();

        let surface = compiler.world().code_surface(user_code).expect("user code indexed");
        let test_form = surface
            .forms
            .iter()
            .find_map(|form| match form {
                ScopeForm::MacroCall(call) => {
                    let head = call
                        .source
                        .cursor()
                        .ast_node(&compiler.world().source_map().borrow())
                        .ok()
                        .flatten()
                        .and_then(|node| node.head.atom_name().ok());
                    (head.as_deref() == Some("test")).then_some(call)
                }
                _ => None,
            })
            .expect("test(...) macro call form in the user surface");

        let true_offset = user_text.find("test(").expect("`test(` appears in the user source") as u32;
        assert_eq!(
            test_form.span.start, true_offset,
            "the test macro call must carry its true byte offset in the user file, not one shifted by a spliced-in prelude"
        );
        assert_eq!(
            test_form.span.source_version,
            compiler.world().source_version(user_code).expect("user source version"),
            "the user node's span must name the user's own code unit, not a combined prelude+user buffer"
        );
    }
}

#[cfg(test)]
mod requested_output_test {
    use super::super::*;

    #[test]
    fn cli_routes_mixed_dump_specs_through_one_file_sink() {
        let dir = std::env::temp_dir().join(format!("fz-cli-dumps-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("create dump directory");
        let specs = [
            (DumpKind::Types, dir.join("root.types")),
            (DumpKind::Activations, dir.join("root.activations")),
            (DumpKind::Backend, dir.join("root.backend")),
            (DumpKind::Native, dir.join("root.native")),
            (DumpKind::Fnir, dir.join("root.fnir")),
        ]
        .map(|(kind, path)| DumpSpec { kind, path });
        let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
        compiler.submit_code(CodeSubmission {
            name: Some("mixed_dumps.fz".to_string()),
            text: "def main(), do: 0\n".to_string(),
        });
        let root = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        compiler.set_requested_output(Box::new(FileRequestedOutput::new(root, &specs)));

        emit_requested_root_dumps(&mut compiler, root, &specs).expect("emit mixed dumps");

        for spec in &specs {
            let text = std::fs::read_to_string(&spec.path).expect("dump file");
            assert!(!text.is_empty(), "empty dump: {}", spec.path.display());
        }
        std::fs::remove_dir_all(dir).ok();
    }
}
