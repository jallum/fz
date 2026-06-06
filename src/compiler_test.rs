use super::*;
use crate::diag::SourceMap;
use crate::modules::pipeline::CompileMode;
use crate::parser::Parser;
use crate::parser::lexer::Lexer;
use crate::telemetry::{Capture, ConfiguredTelemetry};

#[test]
fn compiler_prepares_execution_graph_from_source_and_emits_lto_telemetry() {
    let src = r#"
defmodule Math do
  @spec add(integer, integer) :: integer
  fn add(x, y), do: x + y
end
defmodule User do
  import Math, only: [add: 2]
  @spec run() :: integer
  fn run(), do: add(20, 22)
end
fn main(), do: User.run()
"#;
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz"], capture.handler());
    let mut compiler = Compiler::new();

    let graph = compiler
        .prepare_execution_graph_from_source(src.to_string(), "telemetry.fz".to_string(), &tel, CompileMode::Lto)
        .expect("execution graph");

    assert!(
        graph.module.fn_by_name("main").is_some(),
        "prepared graph should keep main/0"
    );
    assert!(capture.contains(&["fz", "module", "interfaces_collected"]));
    assert!(capture.contains(&["fz", "lto", "interfaces_validated"]));
    assert!(capture.contains(&["fz", "lto", "boundaries_erased"]));
}

#[test]
fn compiler_prepares_execution_graph_from_frontend_output() {
    let src = "fn main(), do: 42";
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler::new();

    let frontend = match compiler.compile_source(src.to_string(), "frontend.fz".to_string(), &tel) {
        Ok(frontend) => frontend,
        Err(_) => panic!("frontend result"),
    };

    let graph = compiler
        .prepare_execution_graph_from_frontend(frontend, &tel, CompileMode::Normal)
        .expect("execution graph from frontend");

    let main_fn = graph.module.fn_by_name("main").expect("main fn");
    assert_eq!(main_fn.name, "main");
}

#[test]
fn compiler_prepares_execution_graph_from_program_input() {
    let src = "fn main(), do: 7";
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler::new();
    let (prog, sm) = parse_program("program.fz", src, &tel);

    let graph = compiler
        .prepare_execution_graph_from_program(prog, sm, &tel, CompileMode::Normal)
        .expect("execution graph from program");

    assert!(
        graph.module.fn_by_name("main").is_some(),
        "program path should keep main/0"
    );
}

fn parse_program(
    source_name: &str,
    src: &str,
    tel: &dyn crate::telemetry::Telemetry,
) -> (crate::ast::Program, SourceMap) {
    let mut sm = SourceMap::new();
    let file_id = sm.add_file(source_name.to_string(), src.to_string());
    let toks = Lexer::with_file_and_source_name(src, file_id, source_name)
        .tokenize(tel)
        .expect("tokenize");
    let prog = Parser::new(toks).parse_program(tel).expect("parse program");
    (prog, sm)
}
