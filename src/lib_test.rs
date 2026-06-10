use super::*;
use exec::runtime::ProcessExitCapture;
use fz_runtime::any_value::NIL_ATOM_ID;
use telemetry::Capture;

// DROP: old-world compile pipeline LTO telemetry, infrastructure
#[test]
fn compile_pipeline_emits_module_and_lto_telemetry() {
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
    let sm_cell = Rc::new(RefCell::new(SourceMap::new()));
    let mut compiler = Compiler::new();

    let _compiled = compile_pipeline(
        &mut compiler,
        &tel,
        &sm_cell,
        src.to_string(),
        "telemetry.fz".to_string(),
        CompileMode::Lto,
    );

    assert!(capture.contains(&["fz", "module", "interfaces_collected"]));
    assert!(capture.contains(&["fz", "lto", "interfaces_validated"]));
    assert!(capture.contains(&["fz", "lto", "boundaries_erased"]));
}

// PICKED: spawn with captured variables executes correctly end-to-end
#[test]
fn compile_pipeline_runs_spawn_with_captures_through_single_plan_path() {
    let tel = ConfiguredTelemetry::new();
    let exits = ProcessExitCapture::new();
    tel.attach(&["fz", "runtime"], exits.handler());
    let sm_cell = Rc::new(RefCell::new(SourceMap::new()));
    let mut compiler = Compiler::new();

    let compiled = compile_pipeline(
        &mut compiler,
        &tel,
        &sm_cell,
        include_str!("../fixtures/spawn_with_captures/input.fz").to_string(),
        "fixtures/spawn_with_captures/input.fz".to_string(),
        CompileMode::Normal,
    );
    let main_fn = compiled.main_fn.expect("main fn");
    let mut rt = Runtime::new(compiled.image.compiled_module(), 1, &tel).with_module(&compiled.module);

    let root_pid = rt.spawn(main_fn);
    rt.run_until_idle();

    let exit = exits.by_pid(root_pid).expect("root process_exited telemetry");
    assert_eq!(
        exit.halt_value, NIL_ATOM_ID as i64,
        "spawn_with_captures should complete successfully through compile_pipeline"
    );
}
