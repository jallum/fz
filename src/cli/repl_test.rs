use super::*;
use crate::telemetry::ConfiguredTelemetry;
use std::collections::VecDeque;
use std::rc::Rc;

struct FakeLineEditor {
    lines: VecDeque<ReplLine>,
    history: Vec<String>,
}

impl FakeLineEditor {
    fn new(lines: impl IntoIterator<Item = ReplLine>) -> Self {
        Self {
            lines: lines.into_iter().collect(),
            history: Vec::new(),
        }
    }
}

impl ReplLineEditor for FakeLineEditor {
    fn read_line(&mut self, _prompt: &str) -> io::Result<ReplLine> {
        Ok(self.lines.pop_front().unwrap_or(ReplLine::Eof))
    }

    fn add_history_entry(&mut self, line: &str) -> io::Result<()> {
        self.history.push(line.to_string());
        Ok(())
    }
}

fn load_program_test(interp: &CompileTimeEvaluator, prog: &Program) -> Result<(), String> {
    let mut t = crate::types::new();
    load_items_filtered(&mut t, interp, prog, false)?;
    load_items_filtered(&mut t, interp, prog, true)?;
    Ok(())
}

fn test_tel() -> Rc<ConfiguredTelemetry> {
    Rc::new(ConfiguredTelemetry::new())
}

fn new_composer() -> ReplComposer {
    ReplComposer::new(test_tel())
}

/// Drive the same session path as the REPL but capture rendered eval
/// results in a vec rather than printing.
fn drive(lines: &[&str]) -> Vec<Result<String, String>> {
    let mut session = ReplSession::new();
    let tel = test_tel();
    let mut composer = ReplComposer::new(tel.clone());
    let mut out: Vec<Result<String, String>> = Vec::new();
    for line in lines {
        match composer.submit_buffer(line) {
            ReplComposerEvent::Empty => {}
            ReplComposerEvent::Quit => break,
            ReplComposerEvent::DocQuery(q) => out.push(Ok(session.lookup_doc(&q))),
            ReplComposerEvent::Diagnostic(msg) => out.push(Err(msg)),
            ReplComposerEvent::Complete(src) => match session.eval_chunk(&src, tel.as_ref()) {
                ReplChunkOutcome::Ok(Some(value)) => {
                    out.push(Ok(session.render_value(value)));
                }
                ReplChunkOutcome::Ok(None) => {
                    out.push(Ok("nil".to_string()));
                }
                ReplChunkOutcome::Err(msg) => {
                    out.push(Err(msg));
                }
            },
        }
    }
    out
}

// PICK: integer arithmetic evaluation in interactive session
#[test]
fn evaluates_simple_expression() {
    let r = drive(&["1 + 2"]);
    assert_eq!(r.len(), 1);
    assert_eq!(r[0].as_deref(), Ok("3"));
}

// DROP: REPL session state and composer mechanics, no compiler2 surface
#[test]
fn drive_uses_composer_for_blank_docs_quit_and_parse_errors() {
    let r = drive(&["", "?missing", "1 2", "3", ":q", "4"]);
    assert_eq!(r.len(), 3);
    assert_eq!(r[0].as_deref(), Ok("missing: not found"));
    assert!(
        matches!(&r[1], Err(msg) if msg.contains("trailing tokens")),
        "{:?}",
        r[1]
    );
    assert_eq!(r[2].as_deref(), Ok("3"));
}

// PICK: integer, float, and mixed-type list display round-trip
#[test]
fn repl_round_trip_int_float_and_mixed_list_display() {
    let r = drive(&["42", "3.14", "[1, 2.5, :a]"]);
    assert_eq!(r[0].as_deref(), Ok("42"));
    assert_eq!(r[1].as_deref(), Ok("3.14"));
    assert_eq!(r[2].as_deref(), Ok("[1, 2.5, :a]"));
}

// PICK: Utf8.valid? and Utf8.from_bytes runtime semantics on binaries
#[test]
fn run_script_str_accepts_utf8_smart_constructors() {
    let src = r#"
fn main() do
  good = <<104, 105>>
  bad = <<0xff, 0xff>>
  assert(Utf8.valid?(good))
  refute(Utf8.valid?(bad) == true)
  assert(Utf8.from_bytes(good) == {:ok, "hi"})
  assert(Utf8.from_bytes(bad) == {:error, :invalid_utf8})
end
"#;
    run_script_str(src).expect("Utf8 helpers should run through script REPL");
}

// PICK: runtime import of Utf8 module; valid? callable in expression
#[test]
fn repl_session_accepts_top_level_runtime_import() {
    let mut session = ReplSession::new();
    let tel = ConfiguredTelemetry::new();
    assert!(matches!(
        session.eval_chunk("import Utf8, only: [valid?: 1]", &tel),
        ReplChunkOutcome::Ok(None)
    ));
    assert_eq!(eval_session_render(&mut session, "valid?(<<104, 105>>)"), "true");
}

// PICK: module alias in scope; qualified call via alias resolves correctly
#[test]
fn repl_session_accepts_top_level_runtime_alias() {
    let mut session = ReplSession::new();
    let tel = ConfiguredTelemetry::new();
    assert!(matches!(
        session.eval_chunk("alias Utf8, as: U", &tel),
        ReplChunkOutcome::Ok(None)
    ));
    assert_eq!(eval_session_render(&mut session, "U.valid?(<<0xff, 0xff>>)"), "false");
}

fn eval_session_i64(session: &mut ReplSession, src: &str) -> Option<i64> {
    let tel = ConfiguredTelemetry::new();
    match session.eval_chunk(src, &tel) {
        ReplChunkOutcome::Ok(Some(value)) => value.as_i64(),
        ReplChunkOutcome::Err(err) => panic!("expected value from `{}`; got err: {}", src, err),
        other => panic!("expected value from `{}`; got {:?}", src, outcome_name(&other)),
    }
}

fn eval_session_render(session: &mut ReplSession, src: &str) -> String {
    let tel = ConfiguredTelemetry::new();
    match session.eval_chunk(src, &tel) {
        ReplChunkOutcome::Ok(Some(value)) => session.render_value(value),
        ReplChunkOutcome::Err(err) => panic!("expected value from `{}`; got err: {}", src, err),
        other => panic!("expected value from `{}`; got {:?}", src, outcome_name(&other)),
    }
}

fn outcome_name(outcome: &ReplChunkOutcome) -> &'static str {
    match outcome {
        ReplChunkOutcome::Ok(Some(_)) => "value",
        ReplChunkOutcome::Ok(None) => "ok",
        ReplChunkOutcome::Err(_) => "err",
    }
}

// DROP: REPL line-editor trait infrastructure, no compiler2 surface
#[test]
fn repl_line_editor_trait_accepts_fake_editor() {
    let mut editor = FakeLineEditor::new([ReplLine::Line("1 + 2".to_string())]);
    assert_eq!(
        editor.read_line("fz> ").expect("read fake line"),
        ReplLine::Line("1 + 2".to_string())
    );
    editor.add_history_entry("1 + 2").expect("record history");
    assert_eq!(editor.history, vec!["1 + 2"]);
    assert_eq!(editor.read_line("fz> ").expect("read eof"), ReplLine::Eof);
}

// DROP: REPL editor validation mechanics, no compiler2 surface
#[test]
fn line_editor_validator_continues_only_parser_incomplete_input() {
    let tel = ConfiguredTelemetry::new();
    assert!(matches!(
        ReplEditorHelper::validation_result_for("do\n  1", &tel),
        ValidationResult::Incomplete
    ));
    assert!(matches!(
        ReplEditorHelper::validation_result_for("do\n  1\nend", &tel),
        ValidationResult::Valid(None)
    ));
    assert!(matches!(
        ReplEditorHelper::validation_result_for("1 2", &tel),
        ValidationResult::Valid(None)
    ));
    assert!(matches!(
        ReplEditorHelper::validation_result_for(":q", &tel),
        ValidationResult::Valid(None)
    ));
    assert!(matches!(
        ReplEditorHelper::validation_result_for("   ", &tel),
        ValidationResult::Valid(None)
    ));
}

// DROP: REPL composer input handling, no compiler2 surface
#[test]
fn composer_ignores_blank_input() {
    let mut composer = new_composer();
    assert_eq!(composer.submit_buffer("   "), ReplComposerEvent::Empty);
}

// DROP: REPL composer quit command, no compiler2 surface
#[test]
fn composer_recognizes_quit_command() {
    let mut composer = new_composer();
    assert_eq!(composer.submit_buffer(":q"), ReplComposerEvent::Quit);
    assert_eq!(composer.submit_buffer(":quit"), ReplComposerEvent::Quit);
}

// DROP: REPL composer docs query dispatch, no compiler2 surface
#[test]
fn composer_recognizes_docs_query() {
    let mut composer = new_composer();
    assert_eq!(
        composer.submit_buffer("? Enum.map"),
        ReplComposerEvent::DocQuery("Enum.map".to_string())
    );
}

// DROP: REPL composer multiline buffering mechanics, no compiler2 surface
#[test]
fn composer_accepts_complete_multiline_item_chunks_from_editor() {
    let mut composer = new_composer();
    assert_eq!(
        composer.submit_buffer(
            r#"@doc "adds one"
fn add1(n), do: n + 1"#
        ),
        ReplComposerEvent::Complete(
            r#"@doc "adds one"
fn add1(n), do: n + 1"#
                .to_string()
        )
    );
}

// DROP: REPL composer multiline expression buffering, no compiler2 surface
#[test]
fn composer_accepts_complete_multiline_expression_chunks_from_editor() {
    let mut composer = new_composer();
    assert_eq!(
        composer.submit_buffer("do\n  1 + 2\nend"),
        ReplComposerEvent::Complete("do\n  1 + 2\nend".to_string())
    );
}

// DROP: REPL composer blank-line preservation, no compiler2 surface
#[test]
fn composer_keeps_blank_lines_inside_submitted_editor_buffer() {
    let mut composer = new_composer();
    assert_eq!(
        composer.submit_buffer("do\n\n  1\nend"),
        ReplComposerEvent::Complete("do\n\n  1\nend".to_string())
    );
}

// DROP: REPL composer error state reset, no compiler2 surface
#[test]
fn composer_reports_invalid_input_without_retaining_state() {
    let mut composer = new_composer();
    assert!(matches!(
        composer.submit_buffer("1 2"),
        ReplComposerEvent::Diagnostic(_)
    ));
    assert_eq!(
        composer.submit_buffer("3"),
        ReplComposerEvent::Complete("3".to_string())
    );
}

// DROP: REPL composer whitespace trimming, no compiler2 surface
#[test]
fn composer_accepts_whitespace_heavy_chunks() {
    let mut composer = new_composer();
    assert_eq!(
        composer.submit_buffer("   fn id(n), do: n   "),
        ReplComposerEvent::Complete("   fn id(n), do: n   ".to_string())
    );
}

// DROP: parser incomplete-input classification, pure infrastructure
#[test]
fn parser_classifies_incomplete_without_error_text() {
    let toks = Lexer::with_source_name("1 +", "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let err = Parser::new(toks).parse_expr_eof().unwrap_err();
    assert!(err.is_incomplete(), "{err}");
}

// DROP: REPL world parse classification mechanics, no compiler2 surface
#[test]
fn repl_world_classifies_eof_shaped_item_input_as_incomplete() {
    let tel = ConfiguredTelemetry::new();
    let err = match ReplWorld::new().parse_chunk(
        r#"
@doc "adds one"
"#,
        &tel,
    ) {
        Ok(_) => panic!("expected incomplete input"),
        Err(err) => err,
    };
    assert!(matches!(err, ReplWorldParse::Incomplete), "{err:?}");
}

// DROP: REPL session composition boundary enforcement, no compiler2 surface
#[test]
fn session_rejects_incomplete_execution_input() {
    let mut session = ReplSession::new();
    let tel = ConfiguredTelemetry::new();
    match session.eval_chunk("do\n  1", &tel) {
        ReplChunkOutcome::Err(msg) => assert!(
            msg.contains("must be composed"),
            "expected composition boundary error, got: {}",
            msg
        ),
        other => panic!("expected composition boundary error, got {:?}", outcome_name(&other)),
    }
}

// DROP: REPL world parse error classification, no compiler2 surface
#[test]
fn repl_world_classifies_invalid_syntax_as_non_incomplete_error() {
    let tel = ConfiguredTelemetry::new();
    let err = match ReplWorld::new().parse_chunk("1 2", &tel) {
        Ok(_) => panic!("expected invalid input"),
        Err(err) => err,
    };
    assert!(
        matches!(&err, ReplWorldParse::Err(msg) if msg.contains("trailing tokens")),
        "{err:?}"
    );
}

// PICK: variable binding persists across sequential evaluation chunks
#[test]
fn repl_session_binds_variable_across_chunks() {
    let mut session = ReplSession::new();
    assert_eq!(eval_session_i64(&mut session, "x = 41"), Some(41));
    assert_eq!(eval_session_i64(&mut session, "x + 1"), Some(42));
}

// PICK: expression evaluation does not rebind existing variables in scope
#[test]
fn repl_session_expression_display_does_not_mutate_frame() {
    let mut session = ReplSession::new();
    assert_eq!(eval_session_i64(&mut session, "x = 10"), Some(10));
    assert_eq!(eval_session_i64(&mut session, "x + 5"), Some(15));
    assert_eq!(eval_session_i64(&mut session, "x"), Some(10));
}

// PICK: tuple destructuring binds multiple names across session chunks
#[test]
fn repl_session_destructuring_binding_persists_across_chunks() {
    let mut session = ReplSession::new();
    assert_eq!(eval_session_render(&mut session, "{a, b} = {1, 2}"), "{1, 2}");
    assert_eq!(eval_session_i64(&mut session, "a + b"), Some(3));
}

// DROP: REPL implementation guard against old wrapper source pattern
#[test]
fn repl_expression_chunks_do_not_depend_on_generated_wrapper_source() {
    let source = std::fs::read_to_string(file!()).expect("read repl source");
    let old_wrapper_shape = ["fn ", "{}({})", " do"].concat();
    assert!(
        !source.contains(&old_wrapper_shape),
        "REPL expression chunks must be compiler-owned entries, not formatted fn source"
    );
    let old_compile_call = ["compile", "_eval", "(&eval", "_source)"].concat();
    assert!(
        !source.contains(&old_compile_call),
        "REPL expression chunks must compile semantic chunk data, not generated eval strings"
    );
}

// DROP: REPL implementation guard against old frame-ABI pattern
#[test]
fn repl_frame_abi_is_not_inferred_by_host_pattern_walkers() {
    let source = std::fs::read_to_string(file!()).expect("read repl source");
    let old_frame_walker = ["fn ", "bound", "_names", "("].concat();
    assert!(
        !source.contains(&old_frame_walker),
        "frame ABI shape must come from compiler-owned lowered locals"
    );
    let old_pattern_walker = ["fn ", "collect", "_pattern", "_names", "("].concat();
    assert!(
        !source.contains(&old_pattern_walker),
        "REPL host must not walk patterns to decide frame updates"
    );
}

// DROP: REPL diagnostic anchoring to user source vs wrapper text
#[test]
fn repl_diagnostics_are_anchored_to_user_source_not_wrapper_text() {
    let mut session = ReplSession::new();
    let tel = ConfiguredTelemetry::new();
    match session.eval_chunk("missing_name + 1", &tel) {
        ReplChunkOutcome::Err(err) => {
            assert!(
                !err.contains("__repl_eval"),
                "diagnostic leaked compiler entry name: {}",
                err
            );
            assert!(
                err.contains("missing_name"),
                "diagnostic should name the user source binding: {}",
                err
            );
        }
        other => panic!("expected diagnostic, got {:?}", outcome_name(&other)),
    }
}

// PICK: whitespace-heavy assignment expression parses and binds correctly
#[test]
fn repl_accepts_whitespace_heavy_multiline_expression_chunks() {
    let mut session = ReplSession::new();
    let src = "\n\n  x\n    =\n      41\n";
    assert_eq!(eval_session_i64(&mut session, src), Some(41));
    assert_eq!(eval_session_i64(&mut session, "x + 1"), Some(42));
}

// PICK: failed pattern match errors and does not corrupt prior bindings
#[test]
fn repl_session_match_failure_uses_lowered_runtime_semantics() {
    let mut session = ReplSession::new();
    assert_eq!(eval_session_i64(&mut session, "x = 1"), Some(1));
    let tel = ConfiguredTelemetry::new();
    match session.eval_chunk("{:ok, y} = {:error, 2}", &tel) {
        ReplChunkOutcome::Err(err) => assert!(
            err.contains("match") || err.contains("clause"),
            "expected match failure diagnostic, got: {}",
            err
        ),
        other => panic!("expected match failure, got {:?}", outcome_name(&other)),
    }
    assert_eq!(eval_session_i64(&mut session, "x"), Some(1));
}

// PICK: top-level fn definition is callable from subsequent expressions
#[test]
fn repl_session_top_level_definition_is_callable() {
    let mut session = ReplSession::new();
    let tel = ConfiguredTelemetry::new();
    assert!(matches!(
        session.eval_chunk("fn add1(n), do: n + 1", &tel),
        ReplChunkOutcome::Ok(None)
    ));
    assert_eq!(eval_session_i64(&mut session, "add1(41)"), Some(42));
}

// DROP: extern declaration accepted in REPL; old-world extern plumbing
#[test]
fn repl_session_accepts_top_level_extern_declaration() {
    let mut session = ReplSession::new();
    let tel = ConfiguredTelemetry::new();
    assert!(matches!(
        session.eval_chunk(r#"extern "C" fn libc::open(cstring, cstring) :: integer"#, &tel,),
        ReplChunkOutcome::Ok(None)
    ));
}

// PICK: spawn/receive/send message passing across sequential session chunks
#[test]
fn repl_session_spawned_child_blocks_across_chunks_and_resumes() {
    let mut session = ReplSession::new();
    assert_eq!(eval_session_i64(&mut session, "parent = self()"), Some(1));
    assert_eq!(
        eval_session_i64(&mut session, "spawn(fn () -> send(parent, receive do x -> x end) end)"),
        Some(2),
    );
    assert_eq!(eval_session_i64(&mut session, "send(2, 42)"), Some(42));
    assert_eq!(eval_session_i64(&mut session, "receive do x -> x end"), Some(42));
}

// PICK: blocked child process survives new fn definition and later message
#[test]
fn repl_session_blocked_child_survives_later_code_generation() {
    let mut session = ReplSession::new();
    assert_eq!(eval_session_i64(&mut session, "parent = self()"), Some(1));
    assert_eq!(
        eval_session_i64(&mut session, "spawn(fn () -> send(parent, receive do x -> x end) end)"),
        Some(2),
    );
    let tel = ConfiguredTelemetry::new();
    assert!(matches!(
        session.eval_chunk("fn id(n), do: n", &tel),
        ReplChunkOutcome::Ok(None)
    ));
    assert_eq!(eval_session_i64(&mut session, "id(42)"), Some(42));
    assert_eq!(eval_session_i64(&mut session, "send(2, 7)"), Some(7));
    assert_eq!(eval_session_i64(&mut session, "receive do x -> x end"), Some(7));
}

// PICK: send to self and receive round-trips a mixed-type list value
#[test]
fn repl_round_trip_send_receive_self() {
    let r = drive(&["send(self(), [1, 2.5, :a])", "receive do x -> x end"]);
    assert_eq!(r[1].as_deref(), Ok("[1, 2.5, :a]"));
}

// PICK: spawned closure sends; receive with pattern match and after clause
#[test]
fn repl_spawned_send_round_trips_through_receive_matcher() {
    let r = drive(&[
        "parent = self()",
        "spawn(fn () -> send(parent, [1, 2.5, :a]) end)",
        r#"receive do
             [1, 2.5, :a] -> :ok
           after
             0 -> :miss
           end"#,
    ]);
    assert_eq!(r[2].as_deref(), Ok(":ok"));
}

// PICK: spawn/2 with heap hint argument sends message correctly
#[test]
fn repl_spawn2_accepts_ignored_heap_hint() {
    let r = drive(&[
        "parent = self()",
        "spawn(fn () -> send(parent, 42) end, 4096)",
        "receive do x -> x end",
    ]);
    assert_eq!(r[2].as_deref(), Ok("42"));
}

// PICK: variable bound in one input chunk used in a later chunk
#[test]
fn binds_variable_across_inputs() {
    let r = drive(&["x = 7", "x + 35"]);
    assert_eq!(r.len(), 2);
    assert_eq!(r[1].as_deref(), Ok("42"));
}

// PICK: multi-clause recursive fn built incrementally across inputs
#[test]
fn appends_clauses_to_existing_fn() {
    let r = drive(&["fn fact(0), do: 1", "fn fact(n), do: n * fact(n - 1)", "fact(6)"]);
    assert!(r[2].as_deref() == Ok("720"), "expected 720, got {:?}", r[2]);
}

// PICK: multiline do-end fn body with local binding evaluates correctly
#[test]
fn accepts_multiline_do_end_from_editor_buffer() {
    let r = drive(&["fn double_plus(x) do\n  y = x + 1\n  y * 2\nend", "double_plus(20)"]);
    let last = r.last().unwrap();
    assert_eq!(last.as_deref(), Ok("42"), "got {:?}", last);
}

/// Drive a full program (lex → parse → flatten → load) and return the
/// interp so doc-lookup tests can inspect post-load state. Mirrors what
/// the REPL does for an item-level input, but in one shot.
fn load(src: &str) -> CompileTimeEvaluator {
    let interp = CompileTimeEvaluator::new();
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    let mut ct = crate::types::new();
    let prog = flatten_modules(&mut ct, prog, &crate::telemetry::ConfiguredTelemetry::new()).expect("resolve");
    for (path, doc) in &prog.module_docs {
        interp.module_docs.borrow_mut().insert(path.clone(), doc.clone());
    }
    load_program_test(&interp, &prog).expect("load");
    interp
}

fn apply_world_item(world: &mut ReplWorld, src: &str) {
    let tel = ConfiguredTelemetry::new();
    match world.parse_chunk(src, &tel).expect("parse world chunk") {
        ReplWorldChunk::Items(prog) => {
            world.apply_items(src, prog, &tel).expect("apply world items");
        }
        ReplWorldChunk::Expr { .. } => panic!("expected item chunk"),
    }
}

fn parse_world_expr(src: &str) -> (Spanned<Expr>, SourceMap) {
    let tel = ConfiguredTelemetry::new();
    match ReplWorld::new().parse_chunk(src, &tel).expect("parse world chunk") {
        ReplWorldChunk::Expr { expr, sm } => (expr, sm),
        ReplWorldChunk::Items(_) => panic!("expected expression chunk"),
    }
}

// DROP: REPL world @doc/@moduledoc lookup mechanics, infrastructure
#[test]
fn repl_world_owns_docs_lookup() {
    let mut world = ReplWorld::new();
    apply_world_item(
        &mut world,
        r#"
defmodule M do
  @moduledoc "the M module"
  @doc "adds two"
  fn add(a, b), do: a + b
end
"#,
    );
    assert_eq!(world.lookup_doc("M"), "the M module");
    assert_eq!(world.lookup_doc("M.add"), "@doc:  adds two");
}

// DROP: REPL world compilation of accumulated clauses, old-world pipeline
#[test]
fn repl_world_compiles_accumulated_item_clauses() {
    let mut world = ReplWorld::new();
    apply_world_item(&mut world, "fn fact(0), do: 1");
    apply_world_item(&mut world, "fn fact(n), do: n * fact(n - 1)");
    let (expr, sm) = parse_world_expr("fact(5)");
    let tel = ConfiguredTelemetry::new();
    let module = world
        .compile_repl_expr(expr, vec![], "__repl_eval_0".to_string(), sm, &tel)
        .expect("compile accumulated clauses");
    assert!(module.module.fn_by_name("__repl_eval_0").is_some());
}

// PICK: defmacro defined in one chunk is expandable in a later expression
#[test]
fn repl_world_compiles_eval_chunks_with_accumulated_macros() {
    let mut world = ReplWorld::new();
    apply_world_item(
        &mut world,
        r#"
defmacro inc(x) do
  quote do: unquote(x) + 1
end
"#,
    );
    let (expr, sm) = parse_world_expr("inc(41)");
    let tel = ConfiguredTelemetry::new();
    let module = world
        .compile_repl_expr(expr, vec![], "__repl_eval_0".to_string(), sm, &tel)
        .expect("compile macro-using eval chunk");
    assert!(module.module.fn_by_name("__repl_eval_0").is_some());
}

// DROP: REPL @doc lookup for module fn, infrastructure not language behaviour
#[test]
fn doc_query_finds_module_fn_doc() {
    let interp = load(
        r#"
defmodule M do
  @doc "adds two"
  fn add(a, b), do: a + b
end
"#,
    );
    assert_eq!(lookup_doc(&interp, "M.add"), "@doc:  adds two");
}

// DROP: REPL @moduledoc lookup, infrastructure not language behaviour
#[test]
fn doc_query_finds_moduledoc() {
    let interp = load(
        r#"
defmodule M do
  @moduledoc "the M module"
  fn add(a, b), do: a + b
end
"#,
    );
    assert_eq!(lookup_doc(&interp, "M"), "the M module");
}

// DROP: REPL @spec surface in doc lookup, infrastructure not language behaviour
#[test]
fn doc_query_surfaces_spec_when_declared() {
    // .31.6 — `?<name>` renders @spec alongside @doc when both are
    // declared.
    let interp = load(
        r#"
defmodule M do
  @doc "adds one"
  @spec add1(integer) :: integer
  fn add1(n), do: n + 1
end
"#,
    );
    let out = lookup_doc(&interp, "M.add1");
    assert!(out.contains("@spec"), "should render @spec line; got: {}", out);
    assert!(out.contains("@doc"), "should render @doc line; got: {}", out);
    // Type display renders integer as `int` (the lattice's name).
    assert!(
        out.contains("(int) -> int"),
        "should render declared types; got: {}",
        out
    );
}

// DROP: REPL @spec-only doc query, infrastructure not language behaviour
#[test]
fn doc_query_surfaces_spec_without_doc() {
    // .31.6 — @spec alone still surfaces in `?<name>`.
    let interp = load(
        r#"
defmodule M do
  @spec add1(integer) :: integer
  fn add1(n), do: n + 1
end
"#,
    );
    let out = lookup_doc(&interp, "M.add1");
    assert!(out.contains("@spec"), "should render @spec line; got: {}", out);
    assert!(
        !out.contains("no documentation"),
        "@spec alone counts as documentation; got: {}",
        out
    );
}

// DROP: REPL multiple @spec rendering in doc query, infrastructure
#[test]
fn doc_query_surfaces_all_declared_specs() {
    let interp = load(
        r#"
defmodule M do
  @spec pick(integer) :: integer
  @spec pick(float) :: float
  fn pick(value), do: value
end
"#,
    );
    let out = lookup_doc(&interp, "M.pick");
    assert_eq!(
        out.lines().filter(|line| line.starts_with("@spec:")).count(),
        2,
        "should render every @spec arrow; got: {}",
        out
    );
    assert!(out.contains("(int) -> int"), "missing integer spec: {out}");
    assert!(out.contains("(float) -> float"), "missing float spec: {out}");
}

// DROP: REPL missing-doc message, infrastructure not language behaviour
#[test]
fn doc_query_missing_doc_reports_so() {
    let interp = load("fn plain(x), do: x");
    assert_eq!(lookup_doc(&interp, "plain"), "plain: no documentation");
}

// DROP: REPL not-found doc message, infrastructure not language behaviour
#[test]
fn doc_query_unknown_name_reports_not_found() {
    let interp = load("fn plain(x), do: x");
    assert_eq!(lookup_doc(&interp, "nope"), "nope: not found");
}

// DROP: REPL empty doc query usage text, infrastructure not language behaviour
#[test]
fn doc_query_empty_shows_usage() {
    let interp = CompileTimeEvaluator::new();
    assert!(lookup_doc(&interp, "").starts_with("usage:"));
}

// ===== fz-i67.1 — run_script_str =====

// PICK: script with main/0 calling a helper fn completes successfully
#[test]
fn run_script_str_accepts_program_with_main() {
    // Defines main/0; run_script_str should call it. (We can't capture
    // stdout from a unit test without subprocessing; the matrix leg in
    // fz-i67.2 covers the stdout side. Here we just verify the driver
    // completes without error.)
    let src = "fn add1(n) do n + 1 end\nfn main() do dbg(add1(41)) end\n";
    run_script_str(src).expect("script with main should succeed");
}

// PICK: multi-process relay program runs through scheduler correctly
#[test]
fn run_script_str_uses_scheduler_backed_relay() {
    let src = std::fs::read_to_string("fixtures/relay/input.fz").expect("read relay fixture");
    run_script_str(&src).expect("relay should run through ir_interp-backed ReplSession");
}

// DROP: script with no main/0 is a no-op; no language behaviour exercised
#[test]
fn run_script_str_accepts_program_without_main() {
    // No main/0 defined → driver finishes without calling anything.
    let src = "fn add1(n) do n + 1 end\n";
    run_script_str(src).expect("script without main should succeed");
}

// PICK: multiline fn body with arithmetic evaluates and runs correctly
#[test]
fn run_script_str_accepts_multi_line_forms() {
    let src = "fn double(x) do\n  x * 2\nend\nfn main() do dbg(double(21)) end\n";
    run_script_str(src).expect("multi-line fn body should parse and run");
}

// PICK: top-level @spec attaches to following fn and program runs
#[test]
fn run_script_str_accepts_top_level_spec_with_fn() {
    let src = "@spec add1(integer) :: integer\nfn add1(n), do: n + 1\nfn main() do dbg(add1(41)) end\n";
    run_script_str(src).expect("top-level @spec should attach to following fn");
}

// DROP: parse error surfaces as Err from script driver, infrastructure
#[test]
fn run_script_str_reports_parse_error() {
    // A syntactically broken input should surface as Err — the matrix
    // leg will translate that into a nonzero exit code.
    let src = "fn main() do dbg(\n"; // unterminated
    let err = run_script_str(src).expect_err("unterminated input should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("parse/expected-token"),
        "expected a parser diagnostic, got: {}",
        msg
    );
}

// PICK: fn redefinition at different arity replaces old; new arity resolves
#[test]
fn redefines_fn_with_different_arity() {
    let r = drive(&["fn f(x), do: x + 1", "fn f(x, y), do: x + y", "f(10, 20)"]);
    // Different arity → replace, not append. f/2 should resolve.
    assert_eq!(r[2].as_deref(), Ok("30"), "got {:?}", r[2]);
}
