//! Compiler2's side-by-side command-line front door.
//!
//! `fz2` stays narrow on purpose: it submits source text, seeds `main/0`,
//! then drives Compiler2's native run/build/interp entry points directly.
//! It does not reopen the old planner/module pipeline or emulate old-world
//! diagnostics.

use std::cell::Cell;
use std::fs::read_to_string;
use std::path::{Path, PathBuf};
use std::process::exit;
use std::rc::Rc;

use crate::aot_link;
use crate::diag::diagnostic::Severity;
use crate::diag::driver::emit_through;
use crate::notify_fixture_execution_start;
use crate::telemetry::{ConfiguredTelemetry, Event, Handler, JsonlBackend, StatsHandler, Value};

use super::{CodeSubmission, Compiler2, ExecutableNeed, RootId, RootSubmission};

pub fn run() {
    let raw_args = std::env::args().skip(1).collect::<Vec<_>>();
    let (log_telemetry, emit_stats, args) = parse_global_args(raw_args);

    let tel = ConfiguredTelemetry::new();
    if let Some(path) = log_telemetry.as_deref() {
        let backend = JsonlBackend::new_file(Path::new(path)).unwrap_or_else(|error| {
            eprintln!("fz2 --log-telemetry {}: {}", path, error);
            exit(2);
        });
        tel.attach(&[], Box::new(backend));
    }
    let stats_handler = if emit_stats {
        let stats = StatsHandler::new();
        tel.attach(&[], stats.handler());
        Some(stats)
    } else {
        None
    };
    let diagnostics = ConsoleDiagnostics::new();
    tel.attach(&["fz", "diag"], diagnostics.handler());

    let exit_code = match dispatch(&tel, args) {
        Ok(()) => 0,
        Err(error) => {
            if !diagnostics.saw_error() {
                eprintln!("{}", error.message);
            }
            error.code
        }
    };

    if let Some(stats) = stats_handler {
        stats.print_summary();
    }
    if exit_code != 0 {
        exit(exit_code);
    }
}

struct CliError {
    code: i32,
    message: String,
}

impl CliError {
    fn usage(message: impl Into<String>) -> Self {
        Self {
            code: 2,
            message: message.into(),
        }
    }

    fn failure(message: impl Into<String>) -> Self {
        Self {
            code: 1,
            message: message.into(),
        }
    }

    fn deferred(message: impl Into<String>) -> Self {
        Self {
            code: 75,
            message: message.into(),
        }
    }
}

fn parse_global_args(raw_args: Vec<String>) -> (Option<String>, bool, Vec<String>) {
    let mut log_telemetry = None;
    let mut emit_stats = false;
    let mut args = Vec::new();
    let mut index = 0;
    while index < raw_args.len() {
        match raw_args[index].as_str() {
            "--log-telemetry" => {
                index += 1;
                log_telemetry = Some(raw_args.get(index).cloned().unwrap_or_else(|| {
                    eprintln!("fz2 --log-telemetry expects a path");
                    exit(2);
                }));
            }
            "--emit=stats" => emit_stats = true,
            _ => args.push(raw_args[index].clone()),
        }
        index += 1;
    }
    (log_telemetry, emit_stats, args)
}

fn dispatch(tel: &ConfiguredTelemetry, args: Vec<String>) -> Result<(), CliError> {
    match args.first().map(String::as_str) {
        Some("help" | "--help" | "-h") => {
            print_help();
            Ok(())
        }
        Some("run") => run_command(tel, &args[1..]),
        Some("interp") => interp_command(tel, &args[1..]),
        Some("build") => build_command(tel, &args[1..]),
        Some(command) => Err(CliError::usage(format!("fz2: unknown command `{command}`"))),
        None => Err(CliError::usage("fz2 <run|build|interp|help> [options] <src.fz>")),
    }
}

fn print_help() {
    print!(
        "\
fz2 — Compiler2 side-by-side front door

Usage:
  fz2 <command> [options] <src.fz>

Commands:
  run     <src.fz>   JIT-compile and run through Compiler2
  build   <src.fz>   AOT-compile and link through Compiler2 (needs -o)
  interp  <src.fz>   run through Compiler2's backend interpreter
  help               show this help (also --help, -h)

Global options (placed before the command):
  --log-telemetry <path>   append JSONL telemetry events to <path>
  --emit=stats             print a stats summary on exit

Compile options (run, build):
  --lto, --whole-program   accepted for compatibility; Compiler2 already
                           closes the root whole-program

build options:
  -o <out>                 output executable path (required)
"
    );
}

fn run_command(tel: &ConfiguredTelemetry, args: &[String]) -> Result<(), CliError> {
    let path = parse_source_path("fz2 run [--lto] <src.fz>", args)?;
    let (mut compiler, root) = load_main_root(tel, &path)?;
    notify_fixture_execution_start();
    compiler
        .run_root_jit(root)
        .map_err(|error| CliError::failure(format!("fz2 run: {error}")))?;
    Ok(())
}

fn interp_command(tel: &ConfiguredTelemetry, args: &[String]) -> Result<(), CliError> {
    let path = match args {
        [path] => PathBuf::from(path),
        _ => return Err(CliError::usage("fz2 interp <src.fz>")),
    };
    let (mut compiler, root) = load_main_root(tel, &path)?;
    notify_fixture_execution_start();
    compiler.run_root_interp(root).map_err(|error| {
        if error.contains("not yet supported") {
            CliError::deferred(format!("fz2 interp: {error}"))
        } else {
            CliError::failure(format!("fz2 interp: {error}"))
        }
    })?;
    Ok(())
}

fn build_command(tel: &ConfiguredTelemetry, args: &[String]) -> Result<(), CliError> {
    let (path, output) = parse_build_args(args)?;
    let (mut compiler, root) = load_main_root(tel, &path)?;
    let obj_name = path.file_stem().and_then(|stem| stem.to_str()).unwrap_or("fz_program");
    let artifact = compiler
        .compile_root_aot(root, obj_name)
        .map_err(|error| CliError::failure(format!("fz2 build: {error}")))?;
    emit_through(tel, None, artifact.diagnostics.as_slice());
    if artifact
        .diagnostics
        .as_slice()
        .iter()
        .any(|diag| diag.severity == Severity::Error)
    {
        return Err(CliError::failure("fz2 build failed with codegen diagnostics"));
    }
    if artifact.main_symbol.is_none() {
        return Err(CliError::failure("fz2 build: no `main/0` fn found"));
    }
    aot_link::link_aot_artifact(&artifact, &output)
        .map_err(|error| CliError::failure(format!("fz2 build: {error}")))?;
    Ok(())
}

fn parse_source_path(usage: &'static str, args: &[String]) -> Result<PathBuf, CliError> {
    let mut path = None;
    for arg in args {
        match arg.as_str() {
            "--lto" | "--whole-program" => {}
            other if !other.starts_with('-') && path.is_none() => path = Some(PathBuf::from(other)),
            other => return Err(CliError::usage(format!("{usage}\nunknown arg `{other}`"))),
        }
    }
    path.ok_or_else(|| CliError::usage(usage))
}

fn parse_build_args(args: &[String]) -> Result<(PathBuf, PathBuf), CliError> {
    let mut path = None;
    let mut output = None;
    let mut index = 0;
    while index < args.len() {
        match args[index].as_str() {
            "--lto" | "--whole-program" => {}
            "-o" => {
                index += 1;
                output = Some(PathBuf::from(
                    args.get(index)
                        .cloned()
                        .ok_or_else(|| CliError::usage("fz2 build [--lto] <src.fz> -o <out>"))?,
                ));
            }
            other if !other.starts_with('-') && path.is_none() => path = Some(PathBuf::from(other)),
            other => {
                return Err(CliError::usage(format!(
                    "fz2 build [--lto] <src.fz> -o <out>\nunknown arg `{other}`"
                )));
            }
        }
        index += 1;
    }
    let path = path.ok_or_else(|| CliError::usage("fz2 build [--lto] <src.fz> -o <out>"))?;
    let output = output.ok_or_else(|| CliError::usage("fz2 build: -o <out> is required"))?;
    Ok((path, output))
}

fn load_main_root<'a>(tel: &'a ConfiguredTelemetry, path: &Path) -> Result<(Compiler2<'a>, RootId), CliError> {
    let source_name = path.display().to_string();
    let text = read_to_string(path).map_err(|error| CliError::failure(format!("read {}: {error}", path.display())))?;
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some(source_name),
        text,
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    Ok((compiler, root))
}

struct ConsoleDiagnostics {
    saw_error: Rc<Cell<bool>>,
}

impl ConsoleDiagnostics {
    fn new() -> Self {
        Self {
            saw_error: Rc::new(Cell::new(false)),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(ConsoleDiagnosticsHandler {
            saw_error: self.saw_error.clone(),
        })
    }

    fn saw_error(&self) -> bool {
        self.saw_error.get()
    }
}

struct ConsoleDiagnosticsHandler {
    saw_error: Rc<Cell<bool>>,
}

impl Handler for ConsoleDiagnosticsHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if !matches!(event.name, ["fz", "diag", "error"] | ["fz", "diag", "warning"]) {
            return;
        }
        let severity = match event.metadata.get("severity") {
            Some(Value::Str(value)) => value.as_ref(),
            _ => "error",
        };
        let code = match event.metadata.get("code") {
            Some(Value::Str(value)) => value.as_ref(),
            _ => "unknown",
        };
        let message = match event.metadata.get("message") {
            Some(Value::Str(value)) => value.as_ref(),
            _ => "diagnostic emitted without a message",
        };
        if severity == "error" {
            self.saw_error.set(true);
        }
        eprintln!("{severity}[{code}]: {message}");
    }
}
