use super::*;
use crate::compiler::{Compiler, ModuleOrigin, ModuleState};
use crate::diag::codes;
use crate::diag::diagnostic::Severity;
use crate::fz_ir::{FnCategory, Term};
use crate::modules::identity::{ExportKey, ModuleName};
use crate::modules::interface::{FZ_INTERFACE_ABI_VERSION, InterfaceFn, InterfaceSpec, ModuleInterface};
use crate::telemetry::{Capture, ConfiguredTelemetry, Event, EventKind, Handler, Value};
use std::cell::RefCell;
use std::rc::Rc;

#[test]
fn returns_warning_diagnostics_without_rendering() {
    let src = "\
fn classify(0), do: :zero
fn classify(1), do: :one
fn main(), do: classify(7)
";
    let out = match compile_source(src.to_string(), "test.fz".to_string()) {
        Ok(out) => out,
        Err(_) => panic!("frontend ok"),
    };
    assert!(
        out.diagnostics
            .as_slice()
            .iter()
            .any(|d| d.code == codes::TYPE_NO_MATCHING_CLAUSE)
    );
}

#[test]
fn returns_error_diagnostics_without_rendering() {
    let err = match compile_source("fn main( do\n".to_string(), "bad.fz".to_string()) {
        Ok(_) => panic!("frontend should fail"),
        Err(err) => err,
    };
    assert!(err.diagnostics.as_slice().iter().any(|d| d.severity == Severity::Error));
}

#[derive(Default)]
struct StructuralFacts {
    parser_items: usize,
    parsed_items: usize,
    lowered_fns: usize,
    typed_specs: usize,
    checked_diagnostics: usize,
}

struct StructuralHandler(Rc<RefCell<StructuralFacts>>);

impl Handler for StructuralHandler {
    fn handle(&self, ev: &Event<'_, '_, '_>) {
        match ev.name {
            ["fz", "parser", "items_built"] => {
                let count = match ev.measurements.get("count") {
                    Some(Value::U64(n)) => *n as usize,
                    _ => 0,
                };
                let mut facts = self.0.borrow_mut();
                facts.parser_items = facts.parser_items.max(count);
            }
            ["fz", "frontend", "parsed"] => {
                if let Some(program) = ev.metadata.get("program").and_then(|v| v.downcast_ref::<Program>()) {
                    self.0.borrow_mut().parsed_items = program.items.len();
                }
            }
            ["fz", "frontend", "lowered"] => {
                if let Some(module) = ev.metadata.get("module").and_then(|v| v.downcast_ref::<Module>()) {
                    self.0.borrow_mut().lowered_fns = module.fns.len();
                }
            }
            ["fz", "planner", "planned"] => {
                if let Some(module_plan) = ev
                    .metadata
                    .get("module_plan")
                    .and_then(|v| v.downcast_ref::<ModulePlan>())
                {
                    self.0.borrow_mut().typed_specs = module_plan.specs.len();
                }
            }
            ["fz", "frontend", "checked"] => {
                let diagnostics = match ev.measurements.get("diagnostics") {
                    Some(Value::U64(n)) => *n as usize,
                    _ => 0,
                };
                self.0.borrow_mut().checked_diagnostics = diagnostics;
            }
            _ => {}
        }
    }
}

fn captured_str<'a>(ev: &'a crate::telemetry::capture::OwnedEvent, key: &str) -> &'a str {
    match ev.metadata.get(key) {
        Some(Value::Str(value)) => value.as_ref(),
        other => panic!("expected string metadata `{key}`, got {other:?}"),
    }
}

fn captured_bool(ev: &crate::telemetry::capture::OwnedEvent, key: &str) -> bool {
    match ev.metadata.get(key) {
        Some(Value::Bool(value)) => *value,
        other => panic!("expected bool metadata `{key}`, got {other:?}"),
    }
}

#[test]
fn structural_telemetry_exposes_compiler_artifacts_to_handlers() {
    let tel = ConfiguredTelemetry::new();
    let facts = Rc::new(RefCell::new(StructuralFacts::default()));
    tel.attach(&["fz"], Box::new(StructuralHandler(facts.clone())));

    let src = "fn id(x), do: x\nfn main(), do: id(1)\n";
    let mut t = crate::types::new();
    let out = match compile_source_with_types(&mut t, src.to_string(), "test.fz".to_string(), &tel) {
        Ok(out) => out,
        Err(_) => panic!("frontend ok"),
    };

    let facts = facts.borrow();
    assert!(
        facts.parser_items >= 2,
        "parser telemetry should expose at least the user program item count"
    );
    assert_eq!(facts.parsed_items, 2);
    assert_eq!(facts.lowered_fns, out.module.fns.len());
    assert_eq!(facts.typed_specs, out.module_plan.specs.len());
    assert_eq!(facts.checked_diagnostics, out.diagnostics.len());
}

#[test]
fn compiler_backed_resolution_reuses_local_module_contracts() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz"], capture.handler());

    let src = r#"
defmodule Math do
  fn add(x, y), do: x + y
end

defmodule User do
  import Math, only: [add: 2]
  fn run(x, y), do: add(x, y)
end
"#;

    let mut compiler = Compiler::new();
    let mut t1 = crate::types::new();
    let first = compile_source_with_compiler_types(
        compiler.world_mut(),
        &mut t1,
        src.to_string(),
        "local_contracts.fz".to_string(),
        &tel,
    )
    .unwrap_or_else(|_| panic!("first compile"));
    let mut t2 = crate::types::new();
    let second = compile_source_with_compiler_types(
        compiler.world_mut(),
        &mut t2,
        src.to_string(),
        "local_contracts.fz".to_string(),
        &tel,
    )
    .unwrap_or_else(|_| panic!("second compile"));

    assert!(first.module.fn_by_name("User.run").is_some());
    assert!(second.module.fn_by_name("User.run").is_some());

    let math = ModuleName::from_segments(vec!["Math".to_string()]);
    let math_id = compiler
        .module_id_for_name(&math)
        .expect("Math should resolve through a compiler-owned module record");
    assert_eq!(compiler.module(math_id).origin, ModuleOrigin::Filesystem);
    assert_eq!(compiler.module(math_id).state, ModuleState::InterfaceReady);

    let requests = capture.find(&["fz", "resolve", "module_contract_requested"]);
    assert!(
        requests.iter().any(|ev| {
            captured_str(ev, "requester_module") == "User"
                && captured_str(ev, "target_module") == "Math"
                && captured_str(ev, "cause") == "import"
        }),
        "resolution telemetry must name the User -> Math import request"
    );

    let ready = capture.find(&["fz", "resolve", "module_contract_ready"]);
    assert!(
        ready.iter().any(|ev| {
            captured_str(ev, "requester_module") == "User"
                && captured_str(ev, "target_module") == "Math"
                && captured_str(ev, "contract_origin") == "filesystem"
                && captured_bool(ev, "compiler_owned")
        }),
        "resolution telemetry must show Math resolving from a compiler-owned filesystem module"
    );

    let root_parsed = capture
        .find(&["fz", "compiler", "parsed"])
        .into_iter()
        .filter(|ev| captured_str(ev, "module_key") == "local_contracts.fz")
        .count();
    assert_eq!(root_parsed, 1, "the root source should parse once across both compiles");

    let math_interface_ready = capture
        .find(&["fz", "compiler", "interface_ready"])
        .into_iter()
        .filter(|ev| captured_str(ev, "module_key") == "Math")
        .count();
    assert_eq!(
        math_interface_ready, 1,
        "Math should reach interface_ready once and then be served from compiler cache"
    );
}

fn parse_with_source_map(src: &str, source_name: &str) -> (Program, SourceMap) {
    let mut sm = SourceMap::new();
    let file_id = sm.add_file(source_name.to_string(), src.to_string());
    let toks = Lexer::with_file(src, file_id).tokenize().expect("lex");
    let prog = Parser::new(toks).parse_program().expect("parse");
    (prog, sm)
}

fn parse_expr_with_source_map(src: &str, source_name: &str) -> (Spanned<Expr>, SourceMap) {
    let mut sm = SourceMap::new();
    let file_id = sm.add_file(source_name.to_string(), src.to_string());
    let toks = Lexer::with_file(src, file_id).tokenize().expect("lex");
    let expr = Parser::new(toks).parse_expr_eof().expect("parse expr");
    (expr, sm)
}

#[test]
fn compile_program_with_types_compiles_parsed_program() {
    let src = "fn id(x), do: x\nfn main(), do: id(41)\n";
    let (prog, sm) = parse_with_source_map(src, "parsed.fz");
    let mut t = crate::types::new();
    let out = match compile_program_with_types(&mut t, prog, sm, &NullTelemetry) {
        Ok(out) => out,
        Err(_) => panic!("compile parsed program"),
    };
    assert!(out.module.fn_by_name("main").is_some());
}

#[test]
fn compile_program_with_types_matches_source_pipeline() {
    let src = "fn add(a, b), do: a + b\nfn main(), do: add(20, 22)\n";
    let source_out = match compile_source(src.to_string(), "source.fz".to_string()) {
        Ok(out) => out,
        Err(_) => panic!("compile source program"),
    };
    let (prog, sm) = parse_with_source_map(src, "source.fz");
    let mut t = crate::types::new();
    let parsed_out = match compile_program_with_types(&mut t, prog, sm, &NullTelemetry) {
        Ok(out) => out,
        Err(_) => panic!("compile parsed program"),
    };
    assert_eq!(parsed_out.module.fns.len(), source_out.module.fns.len());
    assert!(parsed_out.module.fn_by_name("main").is_some());
    assert_eq!(parsed_out.diagnostics.len(), source_out.diagnostics.len());
}

#[test]
fn compile_program_with_types_preserves_diagnostics() {
    let src = "fn main(), do: missing + 1\n";
    let (prog, sm) = parse_with_source_map(src, "bad-parsed.fz");
    let mut t = crate::types::new();
    let err = match compile_program_with_types(&mut t, prog, sm, &NullTelemetry) {
        Ok(_) => panic!("unbound name should fail lowering"),
        Err(err) => err,
    };
    assert!(err.diagnostics.as_slice().iter().any(|d| d.severity == Severity::Error));
}

#[test]
fn compile_source_accepts_loaded_interfaces_without_provider_body() {
    let mut t = crate::types::new();
    let math = ModuleName::from_segments(vec!["Math".to_string()]);
    let mut interfaces = InterfaceTable::new();
    interfaces.insert(
        math.clone(),
        ModuleInterface {
            name: math,
            abi_version: FZ_INTERFACE_ABI_VERSION,
            imports: Vec::new(),
            exports: vec![InterfaceFn {
                name: "add".to_string(),
                arity: 2,
                specs: vec![InterfaceSpec {
                    params: vec!["Ident(\"integer\")".to_string(); 2],
                    result: "Ident(\"integer\")".to_string(),
                }],
                name_span: Span::DUMMY,
            }],
            types: Vec::new(),
            protocols: Vec::new(),
            protocol_impls: Vec::new(),
            docs: None,
            fingerprint_inputs: Vec::new(),
        },
    );
    let src = r#"
defmodule User do
  import Math, only: [add: 2]
  @spec run(integer, integer) :: integer
  fn run(x, y), do: add(x, y)
end
"#;

    let out = match compile_source_with_interface_table(
        &mut t,
        src.to_string(),
        "consumer.fz".to_string(),
        interfaces,
        &NullTelemetry,
    ) {
        Ok(out) => out,
        Err(_) => panic!("frontend ok"),
    };

    assert!(out.module.fn_by_name("User.run").is_some());
    assert!(out.module.fn_by_name("Math.add").is_none());
    assert_eq!(out.module.external_call_edges.len(), 1);
    assert_eq!(
        out.module.external_call_edges[0].target,
        ExportKey::new(ModuleName::from_segments(vec!["Math".to_string()]), "add", 2,)
    );
}

#[test]
fn compile_program_with_types_preserves_macro_expansion() {
    let src = r#"
defmacro inc(x) do
  quote do: unquote(x) + 1
end

fn main(), do: inc(41)
"#;
    let source_out = match compile_source(src.to_string(), "macro-source.fz".to_string()) {
        Ok(out) => out,
        Err(_) => panic!("compile source program"),
    };
    let (prog, sm) = parse_with_source_map(src, "macro-source.fz");
    let mut t = crate::types::new();
    let parsed_out = match compile_program_with_types(&mut t, prog, sm, &NullTelemetry) {
        Ok(out) => out,
        Err(_) => panic!("compile parsed program"),
    };
    assert_eq!(parsed_out.module.fns.len(), source_out.module.fns.len());
    assert!(parsed_out.module.fn_by_name("main").is_some());
}

#[test]
fn compiler_owned_macro_surfaces_are_cached_without_runtime_lowering() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler"], capture.handler());

    let src = r#"
defmodule Macros do
  fn helper(x), do: x + 100
  defmacro bump(x) do
    quote do: helper(unquote(x))
  end
end

defmodule User do
  import Macros, only: [bump: 1]
  fn run(), do: bump(7)
end
"#;

    let mut compiler = Compiler::new();
    let mut t = crate::types::new();
    let first = compile_source_with_compiler_types(
        compiler.world_mut(),
        &mut t,
        src.to_string(),
        "macro-provider.fz".to_string(),
        &tel,
    )
    .unwrap_or_else(|_| panic!("first compile should succeed"));
    let second = compile_source_with_compiler_types(
        compiler.world_mut(),
        &mut t,
        src.to_string(),
        "macro-provider.fz".to_string(),
        &tel,
    )
    .unwrap_or_else(|_| panic!("second compile should reuse compiler cache"));

    assert!(first.module.fn_by_name("User.run").is_some());
    assert!(second.module.fn_by_name("User.run").is_some());

    let macros = ModuleName::parse_dotted("Macros").expect("valid module name");
    let user = ModuleName::parse_dotted("User").expect("valid module name");
    let macros_id = compiler
        .module_id_for_name(&macros)
        .expect("Macros module record should exist");
    let user_id = compiler
        .module_id_for_name(&user)
        .expect("User module record should exist");
    assert_eq!(compiler.module(macros_id).origin, ModuleOrigin::Filesystem);
    assert_eq!(compiler.module(macros_id).state, ModuleState::MacroSurfaceReady);
    assert_eq!(compiler.module(user_id).state, ModuleState::InterfaceReady);

    let parsed_root = capture
        .find(&["fz", "compiler", "parsed"])
        .into_iter()
        .filter(|ev| captured_str(ev, "module_key") == "macro-provider.fz")
        .count();
    assert_eq!(parsed_root, 1, "root source should be parsed once");

    let macro_surfaces = capture
        .find(&["fz", "compiler", "macro_surface_ready"])
        .into_iter()
        .filter(|ev| captured_str(ev, "module_key") == "Macros")
        .count();
    assert_eq!(macro_surfaces, 1, "macro provider should build one surface");
    assert!(
        capture
            .find(&["fz", "compiler", "phase"])
            .into_iter()
            .any(|ev| ev.kind == EventKind::SpanStart && captured_str(&ev, "target_phase") == "macro_surface_ready"),
        "macro provider should execute a macro_surface_ready phase"
    );
    assert!(
        capture
            .find(&["fz", "compiler", "phase"])
            .into_iter()
            .any(|ev| ev.kind == EventKind::SpanStop && ev.measurements.get("elapsed_ns").is_some()),
        "macro-surface phase timing must report elapsed_ns"
    );

    assert!(
        !capture
            .find(&["fz", "compiler", "phase_advanced"])
            .into_iter()
            .filter(|ev| captured_str(ev, "module_key") == "Macros")
            .any(|ev| matches!(captured_str(&ev, "to_phase"), "runtime_lowered" | "runtime_planned")),
        "macro-only provider must not advance into runtime phases"
    );

    compiler
        .validate_invariants()
        .expect("macro-surface compile should leave compiler world consistent");
}

#[test]
fn compile_repl_expr_returns_entry_and_frame_layout_for_plain_expression() {
    let (expr, sm) = parse_expr_with_source_map("x + 1", "repl.fz");
    let mut t = crate::types::new();
    let out = match compile_repl_expr_with_types(
        &mut t,
        Program::default(),
        expr,
        vec!["x".to_string()],
        "__repl_eval_0".to_string(),
        sm,
        &NullTelemetry,
    ) {
        Ok(out) => out,
        Err(_) => panic!("compile repl expression"),
    };
    let entry = out.frontend.module.fn_by_name("__repl_eval_0").expect("repl entry");
    assert_eq!(out.input_frame, vec!["x"]);
    assert_eq!(out.output_frame, vec!["x"]);
    assert_eq!(entry.category, FnCategory::ReplEntry);
}

#[test]
fn compile_repl_expr_extends_frame_for_simple_and_destructuring_bindings() {
    let cases = [
        ("x = 41", Vec::<String>::new(), vec!["x".to_string()]),
        (
            "{a, b} = {1, 2}",
            vec!["z".to_string()],
            vec!["z".to_string(), "a".to_string(), "b".to_string()],
        ),
        ("x = 42", vec!["x".to_string()], vec!["x".to_string()]),
    ];
    for (src, input, expected_output) in cases {
        let (expr, sm) = parse_expr_with_source_map(src, "repl.fz");
        let mut t = crate::types::new();
        let out = match compile_repl_expr_with_types(
            &mut t,
            Program::default(),
            expr,
            input.clone(),
            "__repl_eval_0".to_string(),
            sm,
            &NullTelemetry,
        ) {
            Ok(out) => out,
            Err(_) => panic!("compile repl expression `{}`", src),
        };
        assert_eq!(out.input_frame, input);
        assert_eq!(out.output_frame, expected_output);
    }
}

#[test]
fn compile_repl_expr_lowers_match_failure_path() {
    let (expr, sm) = parse_expr_with_source_map("{:ok, y} = {:error, 2}", "repl.fz");
    let mut t = crate::types::new();
    let out = match compile_repl_expr_with_types(
        &mut t,
        Program::default(),
        expr,
        vec![],
        "__repl_eval_0".to_string(),
        sm,
        &NullTelemetry,
    ) {
        Ok(out) => out,
        Err(_) => panic!("compile repl expression"),
    };
    let entry = out.frontend.module.fn_by_name("__repl_eval_0").expect("repl entry");
    let has_halt = entry
        .blocks
        .iter()
        .any(|block| matches!(block.terminator, Term::Halt(_)));
    assert!(has_halt, "match failure path should lower to Halt");
    assert_eq!(out.output_frame, vec!["y"]);
}
