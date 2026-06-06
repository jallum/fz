use super::*;
use crate::diag::SourceMap;
use crate::exec::runtime::{ProcessExitCapture, Runtime};
use crate::modules::pipeline::CompileMode;
use crate::parser::Parser;
use crate::parser::lexer::Lexer;
use crate::telemetry::{Capture, ConfiguredTelemetry, Value};
use fz_runtime::any_value::NIL_ATOM_ID;

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
    let mut world = World::new();

    compiler
        .prepare_execution_graph_from_source(
            &mut world,
            src.to_string(),
            "telemetry.fz".to_string(),
            &tel,
            CompileMode::Lto,
        )
        .expect("execution graph");

    assert!(
        world.linked_module().fn_by_name("main").is_some(),
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
    let mut world = World::new();

    let frontend = match compiler.compile_source(&mut world, src.to_string(), "frontend.fz".to_string(), &tel) {
        Ok(frontend) => frontend,
        Err(_) => panic!("frontend result"),
    };

    compiler
        .prepare_execution_graph_from_frontend(&mut world, frontend, &tel, CompileMode::Normal)
        .expect("execution graph from frontend");

    let main_fn = world.linked_module().fn_by_name("main").expect("main fn");
    assert_eq!(main_fn.name, "main");
}

#[test]
fn compiler_prepares_execution_graph_from_program_input() {
    let src = "fn main(), do: 7";
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler::new();
    let mut world = World::new();
    let (prog, sm) = parse_program("program.fz", src, &tel);

    compiler
        .prepare_execution_graph_from_program(&mut world, prog, sm, &tel, CompileMode::Normal)
        .expect("execution graph from program");

    assert!(
        world.linked_module().fn_by_name("main").is_some(),
        "program path should keep main/0"
    );
}

#[test]
fn compiler_compile_planned_runs_spawn_with_captures_through_single_plan_path() {
    let tel = ConfiguredTelemetry::new();
    let exits = ProcessExitCapture::new();
    tel.attach(&["fz", "runtime"], exits.handler());
    let mut compiler = Compiler::new();
    let mut world = World::new();

    compiler
        .prepare_execution_graph_from_source(
            &mut world,
            include_str!("../fixtures/spawn_with_captures/input.fz").to_string(),
            "fixtures/spawn_with_captures/input.fz".to_string(),
            &tel,
            CompileMode::Normal,
        )
        .expect("execution graph");
    let compiled = compiler.compile_planned(&mut world, &tel).expect("compile planned");
    let main_fn = world.linked_module().fn_by_name("main").expect("main fn").id;
    let mut rt = Runtime::new(&compiled, 1, &tel).with_module(world.linked_module());

    let root_pid = rt.spawn(main_fn);
    rt.run_until_idle();

    let exit = exits.by_pid(root_pid).expect("root process_exited telemetry");
    assert_eq!(
        exit.halt_value, NIL_ATOM_ID as i64,
        "spawn_with_captures should complete successfully through Compiler::compile_planned"
    );
}

#[test]
fn compiler_compile_planned_consumes_authoritative_plan_without_replanning() {
    let src = "fn main(), do: 42";
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "planner", "planned"], capture.handler());
    let mut compiler = Compiler::new();
    let mut world = World::new();

    compiler
        .prepare_execution_graph_from_source(
            &mut world,
            src.to_string(),
            "planned.fz".to_string(),
            &tel,
            CompileMode::Normal,
        )
        .expect("execution graph");
    let _compiled = compiler.compile_planned(&mut world, &tel).expect("compile planned");

    assert_eq!(
        planner_roles(&capture),
        vec!["frontend_check".to_string(), "linked_execution_graph".to_string()],
        "Compiler native compile should consume the supplied plan without publishing another planner.planned event"
    );
}

#[test]
fn compiler_compile_aot_planned_produces_main_symbol() {
    let src = "fn main(), do: 7";
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler::new();
    let mut world = World::new();

    compiler
        .prepare_execution_graph_from_source(
            &mut world,
            src.to_string(),
            "aot.fz".to_string(),
            &tel,
            CompileMode::Normal,
        )
        .expect("execution graph");
    let artifact = compiler
        .compile_aot_planned(&mut world, "aot_test", &tel)
        .expect("compile aot planned");

    assert!(
        artifact.main_symbol.is_some(),
        "AOT compile should emit a C-callable main symbol"
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

fn planner_roles(cap: &Capture) -> Vec<String> {
    cap.find(&["fz", "planner", "planned"])
        .into_iter()
        .map(|ev| match ev.metadata.get("role") {
            Some(Value::Str(role)) => role.to_string(),
            other => panic!("planner.planned event missing role metadata: {:?}", other),
        })
        .collect()
}
