use super::*;
use crate::diag::codes;
use crate::diag::diagnostic::Severity;
use crate::fz_ir::{FnCategory, Term};
use crate::modules::identity::{ExportKey, ModuleName};
use crate::modules::interface::{FZ_INTERFACE_ABI_VERSION, InterfaceFn, InterfaceSpec, ModuleInterface};
use crate::telemetry::{ConfiguredTelemetry, Event, Handler, Value};
use std::cell::RefCell;
use std::rc::Rc;

fn compile_source(src: String, source_name: String) -> FrontendResult {
    let mut t = crate::types::new();
    let tel = ConfiguredTelemetry::new();
    compile_source_with_types(&mut t, src, source_name, &tel)
}

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
                self.0.borrow_mut().parser_items = count;
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
    assert_eq!(facts.parser_items, 2);
    assert_eq!(facts.parsed_items, 2);
    assert_eq!(facts.lowered_fns, out.module.fns.len());
    assert_eq!(facts.typed_specs, out.module_plan.specs.len());
    assert_eq!(facts.checked_diagnostics, out.diagnostics.len());
}

fn parse_with_source_map(src: &str, source_name: &str) -> (Program, SourceMap) {
    let mut sm = SourceMap::new();
    let file_id = sm.add_file(source_name.to_string(), src.to_string());
    let toks = Lexer::with_file_and_source_name(src, file_id, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    (prog, sm)
}

fn parse_expr_with_source_map(src: &str, source_name: &str) -> (Spanned<Expr>, SourceMap) {
    let mut sm = SourceMap::new();
    let file_id = sm.add_file(source_name.to_string(), src.to_string());
    let toks = Lexer::with_file_and_source_name(src, file_id, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let expr = Parser::new(toks).parse_expr_eof().expect("parse expr");
    (expr, sm)
}

#[test]
fn compile_program_with_types_compiles_parsed_program() {
    let src = "fn id(x), do: x\nfn main(), do: id(41)\n";
    let (prog, sm) = parse_with_source_map(src, "parsed.fz");
    let mut t = crate::types::new();
    let out = match compile_program_with_types(&mut t, prog, sm, &crate::telemetry::ConfiguredTelemetry::new()) {
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
    let parsed_out = match compile_program_with_types(&mut t, prog, sm, &crate::telemetry::ConfiguredTelemetry::new()) {
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
    let err = match compile_program_with_types(&mut t, prog, sm, &crate::telemetry::ConfiguredTelemetry::new()) {
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
        &crate::telemetry::ConfiguredTelemetry::new(),
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
    let parsed_out = match compile_program_with_types(&mut t, prog, sm, &crate::telemetry::ConfiguredTelemetry::new()) {
        Ok(out) => out,
        Err(_) => panic!("compile parsed program"),
    };
    assert_eq!(parsed_out.module.fns.len(), source_out.module.fns.len());
    assert!(parsed_out.module.fn_by_name("main").is_some());
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
        &crate::telemetry::ConfiguredTelemetry::new(),
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
            &crate::telemetry::ConfiguredTelemetry::new(),
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
        &crate::telemetry::ConfiguredTelemetry::new(),
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
