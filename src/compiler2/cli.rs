//! Compiler2's side-by-side command-line front door.
//!
//! `fz2` stays narrow on purpose: it submits source text, seeds `main/0`,
//! then drives Compiler2's native run/build/interp entry points directly.
//! It does not reopen the old planner/module pipeline or emulate old-world
//! diagnostics.

use std::fs::read_to_string;
use std::path::{Path, PathBuf};
use std::process::{Command, exit};
use std::time::Duration;

use crate::aot_link;
use crate::diag::diagnostic::Severity;
use crate::diag::driver::emit_through;
use crate::diag::style::ColorMode;
use crate::notify_fixture_execution_start;
use crate::telemetry::diag_render::{DiagRenderer, DiagnosticStatus};
use crate::telemetry::{ConfiguredTelemetry, JsonlBackend, StatsHandler};

use super::code::CodeId;
use super::dump::{DumpKind, DumpSpec, FileRequestedOutput, max_requested_stage, parse_dump_spec};
use super::quoted_surface::{MacroCallForm, ScopeForm, ScopeSurface, read_module_body_surface, read_scope_surface};
use super::{CodeSubmission, Compiler2, ExecutableNeed, RootId, RootSubmission, parse_quoted_program};

// Keep the frontdoor drive budget aligned with the slowest fixture path budget;
// larger Enum protocol frontiers can legitimately take more than five seconds
// to close before native/backend blockers are observable.
const FZ2_COMPILER_DRIVE_TIMEOUT: Duration = Duration::from_secs(15);

pub fn run() {
    let raw_args = std::env::args().skip(1).collect::<Vec<_>>();
    let (log_telemetry, emit_stats, args) = parse_global_args(raw_args);

    let tel = ConfiguredTelemetry::new();
    if let Some(path) = log_telemetry.as_deref() {
        let backend = JsonlBackend::new_public_file(Path::new(path)).unwrap_or_else(|error| {
            eprintln!("fz2 --log-telemetry {}: {}", path, error);
            exit(2);
        });
        backend.install(&tel);
    }
    let stats_handler = if emit_stats {
        let stats = StatsHandler::new();
        stats.install(&tel);
        Some(stats)
    } else {
        None
    };
    let diagnostic_status = DiagnosticStatus::new();

    let exit_code = match dispatch(tel, args, &diagnostic_status) {
        Ok(()) => 0,
        Err(error) => {
            if !diagnostic_status.saw_error() {
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

fn dispatch(tel: ConfiguredTelemetry, args: Vec<String>, diagnostic_status: &DiagnosticStatus) -> Result<(), CliError> {
    // Stress settings fail eagerly, on every run: the lazy thread-local
    // parse fires only when a perturbation site is reached, and a typo'd
    // sweep reading green on the fixtures that never get there is exactly
    // the silent-inert failure the grammar's panic exists to rule out
    // (fz-kdt.141 refutation: 421/584 fixtures completed under a typo).
    super::callsite_dispatch::dispatch_stress::validate_env().map_err(CliError::usage)?;
    match args.first().map(String::as_str) {
        Some("help" | "--help" | "-h") => {
            print_help();
            Ok(())
        }
        Some("run") => run_command(tel, &args[1..], diagnostic_status),
        Some("interp") => interp_command(tel, &args[1..], diagnostic_status),
        Some("build") => build_command(tel, &args[1..], diagnostic_status),
        Some("test") => test_command(tel, &args[1..], diagnostic_status),
        // Not advertised in `help`: the private per-test entry point `test_command`
        // spawns itself through, one subprocess per discovered test, so a failing
        // `assert` (which aborts the process on the JIT backend) can't take down
        // sibling tests.
        Some("run-test-root") => run_test_root_command(tel, &args[1..], diagnostic_status),
        Some(command) => Err(CliError::usage(format!("fz2: unknown command `{command}`"))),
        None => Err(CliError::usage("fz2 <run|build|interp|test|help> [options] <src.fz>")),
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
  test    <src.fz>   discover and run every `test(:name) do ... end` in the
                     source (top-level or nested in a `defmodule`), one
                     subprocess per test; add --interp to run each test
                     through the backend interpreter instead of the JIT
  help               show this help (also --help, -h)

Global options (placed before the command):
  --log-telemetry <path>   append JSONL telemetry events to <path>
  --emit=stats             print a stats summary on exit

Compile options (run, build):
  --lto, --whole-program   accepted for compatibility; Compiler2 already
                           closes the root whole-program
  --dump <spec>            install one dump sink; spec is either <path>
                           (kind inferred from extension) or <kind>=<path>

build options:
  -o <out>                 output executable path (required)
"
    );
}

fn run_command(
    tel: ConfiguredTelemetry,
    args: &[String],
    diagnostic_status: &DiagnosticStatus,
) -> Result<(), CliError> {
    let options = parse_source_options("fz2 run [--lto] [--dump <spec>] <src.fz>", args)?;
    let path = options.path;
    let (mut compiler, root) = load_main_root(tel, &path, diagnostic_status)?;
    compiler.set_requested_output(Box::new(FileRequestedOutput::new(root, &options.dumps)));
    emit_requested_root_dumps(&mut compiler, root, &options.dumps).map_err(CliError::failure)?;
    notify_fixture_execution_start();
    compiler
        .run_root_jit(root)
        .map_err(|error| CliError::failure(format!("fz2 run: {error}")))?;
    Ok(())
}

fn interp_command(
    tel: ConfiguredTelemetry,
    args: &[String],
    diagnostic_status: &DiagnosticStatus,
) -> Result<(), CliError> {
    let options = parse_source_options("fz2 interp [--dump <spec>] <src.fz>", args)?;
    let path = options.path;
    let (mut compiler, root) = load_main_root(tel, &path, diagnostic_status)?;
    compiler.set_requested_output(Box::new(FileRequestedOutput::new(root, &options.dumps)));
    emit_requested_root_dumps(&mut compiler, root, &options.dumps).map_err(CliError::failure)?;
    notify_fixture_execution_start();
    let result = compiler.run_root_interp(root).map_err(|error| {
        if error.contains("not yet supported") {
            CliError::deferred(format!("fz2 interp: {error}"))
        } else {
            CliError::failure(format!("fz2 interp: {error}"))
        }
    });
    result?;
    Ok(())
}

fn build_command(
    tel: ConfiguredTelemetry,
    args: &[String],
    diagnostic_status: &DiagnosticStatus,
) -> Result<(), CliError> {
    let mut compiler = configured_compiler(tel, diagnostic_status);
    (|| {
        let options = parse_build_options(args)?;
        let path = options.path;
        let output = options.output;
        let root = submit_main_root_from_path(&mut compiler, &path)?;
        compiler.set_requested_output(Box::new(FileRequestedOutput::new(root, &options.dumps)));
        emit_requested_root_dumps(&mut compiler, root, &options.dumps).map_err(CliError::failure)?;
        let obj_name = path.file_stem().and_then(|stem| stem.to_str()).unwrap_or("fz_program");
        let artifact = compiler
            .compile_root_aot(root, obj_name)
            .map_err(|error| CliError::failure(format!("fz2 build: {error}")))?;
        emit_through(compiler.telemetry(), artifact.diagnostics.as_slice());
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
        aot_link::link_aot_artifact(&artifact, &output, compiler.telemetry())
            .map_err(|error| CliError::failure(format!("fz2 build: {error}")))?;
        Ok(())
    })()
}

/// `fz2 test <src.fz>`: discovers every `test(:name) do ... end` item — at
/// top level or nested in a `defmodule` — and runs each as its own root.
/// Each test runs in a fresh `run-test-root` subprocess: on the JIT backend a
/// failing `assert` aborts the whole process (see `fz_panic`), so sibling
/// tests would never run if the driver executed them in-process.
fn test_command(
    tel: ConfiguredTelemetry,
    args: &[String],
    _diagnostic_status: &DiagnosticStatus,
) -> Result<(), CliError> {
    let options = parse_test_options(args)?;
    let path = options.path;
    let text = read_to_string(&path).map_err(|error| CliError::failure(format!("read {}: {error}", path.display())))?;
    let source_name = path.display().to_string();
    let tests =
        discover_tests(&source_name, &text, &tel).map_err(|error| CliError::failure(format!("fz2 test: {error}")))?;
    let exe = std::env::current_exe().map_err(|error| CliError::failure(format!("fz2 test: {error}")))?;

    println!("Running {}...\n", plural_count(tests.len(), "test", "tests"));
    notify_fixture_execution_start();
    let mut failures = 0usize;
    for test in &tests {
        let module_arg = test.module_arg();
        let mut command = Command::new(&exe);
        command.arg("run-test-root").arg(&path).arg(&module_arg).arg(&test.name);
        if options.interp {
            command.arg("--interp");
        }
        let status = command
            .status()
            .map_err(|error| CliError::failure(format!("fz2 test: spawn `run-test-root`: {error}")))?;
        if status.success() {
            println!("  ok  {}", test.display_name());
        } else {
            failures += 1;
            println!("  failed  {}", test.display_name());
        }
    }
    println!(
        "\n{}, {}",
        plural_count(tests.len(), "test", "tests"),
        plural_count(failures, "failure", "failures")
    );
    if failures > 0 {
        return Err(CliError::failure(format!(
            "fz2 test: {failures} of {} tests failed",
            tests.len()
        )));
    }
    Ok(())
}

fn plural_count(count: usize, singular: &str, plural: &str) -> String {
    format!("{count} {}", if count == 1 { singular } else { plural })
}

/// The `test(:name) do ... end` item macro. Not part of the `Kernel` prelude
/// (adding it there would grow the shared bootstrap's reachable-function count
/// for every fz2 program, not just ones that use `test`). `fz2 test` instead
/// registers it as a scoped prelude on the test root's own world — its own
/// `CodeId`, scoped in over the runtime prelude — so the user's test file is
/// submitted verbatim with its true on-disk spans intact. It expands to a
/// plain `fn <name>(), do: <body>` through the same `Fz.Compiler.define` path
/// every other definition takes, the identical shape `fn`/`defmodule` use in
/// `runtime.fz`.
const TEST_MACRO_PRELUDE_SOURCE: &str = "\
defmacro test(name_atom, [do: body]) do
  source = {:fn, %{}, [{name_atom, %{}, []}, [{:do, body}]]}
  quote do: Fz.Compiler.define(unquote(source), unquote(__CALLER__))
end
";

/// Source name the test-macro scoped prelude is submitted under. Its own file
/// identity keeps its spans (and any diagnostics it raises) distinct from the
/// user's source, which is submitted verbatim under its own path.
const TEST_MACRO_PRELUDE_NAME: &str = "test:prelude.fz";

/// Private per-test entry point that `test_command` spawns as a subprocess:
/// submits exactly one test's fn (module-qualified when the test lives inside
/// a `defmodule`) as a root and runs it — JIT by default, `--interp` to run it
/// through the backend interpreter instead. The `test` item macro is supplied
/// as a scoped prelude (its own `CodeId`), never spliced into the user source,
/// so the user's file keeps its true byte offsets.
fn run_test_root_command(
    tel: ConfiguredTelemetry,
    args: &[String],
    diagnostic_status: &DiagnosticStatus,
) -> Result<(), CliError> {
    let usage = "fz2 run-test-root [--interp] <src.fz> <module|-> <name>";
    let mut interp = false;
    let mut positional = Vec::new();
    for arg in args {
        match arg.as_str() {
            "--interp" => interp = true,
            other => positional.push(other),
        }
    }
    let [path, module_arg, name] = positional[..] else {
        return Err(CliError::usage(usage));
    };
    let module_name = (module_arg != "-").then(|| module_arg.to_string());
    let path = Path::new(path);
    let source_name = path.display().to_string();
    let text = read_to_string(path).map_err(|error| CliError::failure(format!("read {}: {error}", path.display())))?;
    let (mut compiler, root) = load_test_root_from_text(
        tel,
        source_name,
        text,
        module_name,
        name.to_string(),
        0,
        diagnostic_status,
    );
    if interp {
        compiler
            .run_root_interp(root)
            .map_err(|error| CliError::failure(format!("fz2 test: {error}")))?;
    } else {
        compiler
            .run_root_jit(root)
            .map_err(|error| CliError::failure(format!("fz2 test: {error}")))?;
    }
    Ok(())
}

struct TestOptions {
    path: PathBuf,
    interp: bool,
}

fn parse_test_options(args: &[String]) -> Result<TestOptions, CliError> {
    let usage = "fz2 test [--interp] <src.fz>";
    let mut path = None;
    let mut interp = false;
    for arg in args {
        match arg.as_str() {
            "--interp" => interp = true,
            other if !other.starts_with('-') && path.is_none() => path = Some(PathBuf::from(other)),
            other => return Err(CliError::usage(format!("{usage}\nunknown arg `{other}`"))),
        }
    }
    let path = path.ok_or_else(|| CliError::usage(usage))?;
    Ok(TestOptions { path, interp })
}

/// One discovered `test(:name) do ... end` item, qualified by the
/// `defmodule` path it is nested in (empty for a top-level test).
struct DiscoveredTest {
    module_path: Vec<String>,
    name: String,
}

impl DiscoveredTest {
    fn display_name(&self) -> String {
        if self.module_path.is_empty() {
            self.name.clone()
        } else {
            format!("{}.{}", self.module_path.join("."), self.name)
        }
    }

    /// The `submit_root` module name (`.`-joined), or `-` when the test is
    /// top-level — the sentinel `run-test-root` decodes back to `None`.
    fn module_arg(&self) -> String {
        if self.module_path.is_empty() {
            "-".to_string()
        } else {
            self.module_path.join(".")
        }
    }
}

/// Reads the source's top-level surface (and every nested `defmodule` body)
/// to find `test(:name) do ... end` items, without running any semantic
/// compilation. `test` is an ordinary `defmacro` (from the `Kernel` prelude)
/// expanding to a plain `fn`, so at this pre-expansion read it is just an
/// item-position macro call named `test` whose first argument is the atom
/// naming the fn it will define; real compilation (via `load_root`) expands
/// and defines it exactly as any other item macro would.
fn discover_tests(source_name: &str, text: &str, tel: &ConfiguredTelemetry) -> Result<Vec<DiscoveredTest>, String> {
    let quoted_root = parse_quoted_program(source_name, text, CodeId::ZERO, tel).map_err(|error| format!("{error}"))?;
    let surface = read_scope_surface(&quoted_root).map_err(|error| format!("{error}"))?;
    let mut module_path = Vec::new();
    let mut tests = Vec::new();
    collect_tests(&surface, &mut module_path, &mut tests)?;
    tests.sort_by_key(DiscoveredTest::display_name);
    Ok(tests)
}

fn collect_tests(
    surface: &ScopeSurface,
    module_path: &mut Vec<String>,
    out: &mut Vec<DiscoveredTest>,
) -> Result<(), String> {
    for form in &surface.forms {
        match form {
            // A pre-expansion user read never yields `ScopeForm::Module`
            // (`defmodule` is itself just an item-position macro call, per
            // `quoted_surface::build_form`) but handle it defensively in case
            // a future canonicalized read ever lands here.
            ScopeForm::Module(module) => {
                module_path.push(module.name.clone());
                let nested_result = read_module_body_surface(module)
                    .map_err(|error| format!("{error}"))
                    .and_then(|nested| collect_tests(&nested, module_path, out));
                module_path.pop();
                nested_result?;
            }
            ScopeForm::MacroCall(macro_call) => {
                collect_from_macro_call(macro_call, module_path, out)?;
            }
            _ => {}
        }
    }
    Ok(())
}

/// A pre-expansion item-position call is one of: `test(<atom>, ...)`
/// (recorded as a discovered test), `defmodule <alias> do ... end` (recursed
/// into with the alias pushed onto `module_path`), or anything else (a
/// user-defined macro, `defprotocol`, etc. — not test-shaped, skipped).
fn collect_from_macro_call(
    macro_call: &MacroCallForm,
    module_path: &mut Vec<String>,
    out: &mut Vec<DiscoveredTest>,
) -> Result<(), String> {
    let cursor = macro_call.source.cursor();
    let Some(node) = cursor.ast_node().map_err(|error| error.to_string())? else {
        return Ok(());
    };
    let Ok(head) = node.head.atom_name() else {
        return Ok(());
    };
    match head.as_str() {
        "test" => {
            // Only a `test(<atom>, [do: ...])` shape is a test the macro can
            // expand. A non-atom name (`test("x") do ... end`) or a second
            // argument that is not a `do`-keyword list (`test(:t, 42)`) is not
            // this macro's shape, so it is skipped here rather than discovered
            // and left to blow up opaquely inside macro expansion.
            let args = node.tail.list_items().map_err(|error| error.to_string())?;
            let name = args.first().and_then(|first| first.atom_name().ok());
            // A second argument that is not a `do`-keyword list (e.g. a bare
            // int) simply is not a do-body, so a read error here means "not a
            // test", not a hard failure.
            let has_do_body = args
                .get(1)
                .and_then(|kwargs| do_keyword_body_root(&macro_call.source, kwargs).ok().flatten())
                .is_some();
            if let (Some(name), true) = (name, args.len() == 2 && has_do_body) {
                out.push(DiscoveredTest {
                    module_path: module_path.clone(),
                    name,
                });
            }
            Ok(())
        }
        "defmodule" => {
            let args = node.tail.list_items().map_err(|error| error.to_string())?;
            let Some(alias) = args.first() else {
                return Ok(());
            };
            let Some(kwargs) = args.get(1) else {
                return Ok(());
            };
            let module_name = module_alias_name(alias).map_err(|error| error.to_string())?;
            let Some(module_name) = module_name else {
                return Ok(());
            };
            let body_root = do_keyword_body_root(&macro_call.source, kwargs).map_err(|error| error.to_string())?;
            let Some(body_root) = body_root else {
                return Ok(());
            };
            let nested = read_scope_surface(&body_root).map_err(|error| format!("{error}"))?;
            module_path.push(module_name);
            let result = collect_tests(&nested, module_path, out);
            module_path.pop();
            result
        }
        _ => Ok(()),
    }
}

/// Reads a quoted `__aliases__` node (e.g. `MathTest`, `A.B`) into its
/// dotted name. `None` (rather than an error) for anything that isn't an
/// alias — a `defmodule` head this malformed will fail properly at real
/// compile time; discovery just skips it.
fn module_alias_name(
    cursor: &super::source::QuotedSourceCursor,
) -> Result<Option<String>, super::source::QuotedSourceError> {
    let Some(node) = cursor.ast_node()? else {
        return Ok(None);
    };
    if node.head.atom_name().ok().as_deref() != Some("__aliases__") {
        return Ok(None);
    }
    Ok(Some(node.tail.list_atom_names()?.join(".")))
}

/// Given a call's trailing keyword-list argument, returns the `:do` entry's
/// value root (the module/fn body), or `None` if there is no `do:` entry.
fn do_keyword_body_root(
    owner: &super::source::QuotedSourceRoot,
    kwargs: &super::source::QuotedSourceCursor,
) -> Result<Option<super::source::QuotedSourceRoot>, super::source::QuotedSourceError> {
    for entry in kwargs.list_items()? {
        let tuple = entry.tuple_items()?;
        if tuple.len() == 2 && tuple[0].atom_name()? == "do" {
            return Ok(Some(owner.subroot(tuple[1].root())));
        }
    }
    Ok(None)
}

struct SourceOptions {
    path: PathBuf,
    dumps: Vec<DumpSpec>,
}

struct BuildOptions {
    path: PathBuf,
    output: PathBuf,
    dumps: Vec<DumpSpec>,
}

fn parse_source_options(usage: &'static str, args: &[String]) -> Result<SourceOptions, CliError> {
    let mut path = None;
    let mut dumps = Vec::new();
    let mut index = 0;
    while index < args.len() {
        match args[index].as_str() {
            "--lto" | "--whole-program" => {}
            "--dump" => {
                index += 1;
                let spec = args
                    .get(index)
                    .ok_or_else(|| CliError::usage(format!("{usage}\n--dump expects a spec")))?;
                dumps.push(parse_dump_spec(spec).map_err(CliError::usage)?);
            }
            other if !other.starts_with('-') && path.is_none() => path = Some(PathBuf::from(other)),
            other => return Err(CliError::usage(format!("{usage}\nunknown arg `{other}`"))),
        }
        index += 1;
    }
    let path = path.ok_or_else(|| CliError::usage(usage))?;
    Ok(SourceOptions { path, dumps })
}

fn parse_build_options(args: &[String]) -> Result<BuildOptions, CliError> {
    let mut path = None;
    let mut output = None;
    let mut dumps = Vec::new();
    let mut index = 0;
    while index < args.len() {
        match args[index].as_str() {
            "--lto" | "--whole-program" => {}
            "--dump" => {
                index += 1;
                let spec = args.get(index).ok_or_else(|| {
                    CliError::usage("fz2 build [--lto] [--dump <spec>] <src.fz> -o <out>\n--dump expects a spec")
                })?;
                dumps.push(parse_dump_spec(spec).map_err(CliError::usage)?);
            }
            "-o" => {
                index += 1;
                output = Some(PathBuf::from(args.get(index).cloned().ok_or_else(|| {
                    CliError::usage("fz2 build [--lto] [--dump <spec>] <src.fz> -o <out>")
                })?));
            }
            other if !other.starts_with('-') && path.is_none() => path = Some(PathBuf::from(other)),
            other => {
                return Err(CliError::usage(format!(
                    "fz2 build [--lto] [--dump <spec>] <src.fz> -o <out>\nunknown arg `{other}`"
                )));
            }
        }
        index += 1;
    }
    let path = path.ok_or_else(|| CliError::usage("fz2 build [--lto] [--dump <spec>] <src.fz> -o <out>"))?;
    let output = output.ok_or_else(|| CliError::usage("fz2 build: -o <out> is required"))?;
    Ok(BuildOptions { path, output, dumps })
}

fn emit_requested_root_dumps(
    compiler: &mut Compiler2<ConfiguredTelemetry>,
    root: RootId,
    dumps: &[DumpSpec],
) -> Result<(), String> {
    if let Some(stage) = max_requested_stage(dumps) {
        compiler
            .drive_root_to_dump_stage(root, stage)
            .map_err(|error| format!("fz2 dump prep: {error}"))?;
        compiler.emit_requested_program_dumps(root);
    }
    // The types/activations dumps are served from the product-path activation
    // inventory, independently of any backend/native stage drive above, so they
    // never depend on a root-wide semantic inventory.
    if dumps
        .iter()
        .any(|spec| matches!(spec.kind, DumpKind::Types | DumpKind::Activations))
    {
        compiler
            .emit_product_semantic_dumps(root)
            .map_err(|error| format!("fz2 dump prep: {error}"))?;
    }
    Ok(())
}

fn load_main_root(
    tel: ConfiguredTelemetry,
    path: &Path,
    diagnostic_status: &DiagnosticStatus,
) -> Result<(Compiler2<ConfiguredTelemetry>, RootId), CliError> {
    load_root(tel, path, None, "main".to_string(), 0, diagnostic_status)
}

fn load_root(
    tel: ConfiguredTelemetry,
    path: &Path,
    module_name: Option<String>,
    name: String,
    arity: usize,
    diagnostic_status: &DiagnosticStatus,
) -> Result<(Compiler2<ConfiguredTelemetry>, RootId), CliError> {
    let mut compiler = configured_compiler(tel, diagnostic_status);
    let root = submit_root_from_path(&mut compiler, path, module_name, name, arity)?;
    Ok((compiler, root))
}

fn configured_compiler(
    tel: ConfiguredTelemetry,
    diagnostic_status: &DiagnosticStatus,
) -> Compiler2<ConfiguredTelemetry> {
    let mut compiler = Compiler2::new(tel);
    DiagRenderer::new_to_stderr_with_status(
        compiler.source_map(),
        diagnostic_color_mode(),
        diagnostic_status.clone(),
    )
    .install(compiler.telemetry());
    compiler.set_drive_timeout(FZ2_COMPILER_DRIVE_TIMEOUT);
    compiler
}

fn submit_main_root_from_path(compiler: &mut Compiler2<ConfiguredTelemetry>, path: &Path) -> Result<RootId, CliError> {
    submit_root_from_path(compiler, path, None, "main".to_string(), 0)
}

fn submit_root_from_path(
    compiler: &mut Compiler2<ConfiguredTelemetry>,
    path: &Path,
    module_name: Option<String>,
    name: String,
    arity: usize,
) -> Result<RootId, CliError> {
    let source_name = path.display().to_string();
    let text = read_to_string(path).map_err(|error| CliError::failure(format!("read {}: {error}", path.display())))?;
    Ok(submit_root_from_text(
        compiler,
        source_name,
        text,
        module_name,
        name,
        arity,
    ))
}

fn submit_root_from_text(
    compiler: &mut Compiler2<ConfiguredTelemetry>,
    source_name: String,
    text: String,
    module_name: Option<String>,
    name: String,
    arity: usize,
) -> RootId {
    compiler.submit_code(CodeSubmission {
        name: Some(source_name),
        text,
    });
    compiler.submit_root(RootSubmission {
        module_name,
        name,
        arity,
        need: ExecutableNeed::Value,
    })
}

/// Like ordinary root setup but first registers the `test` item macro as a
/// scoped prelude, so the submitted test source — passed verbatim, spans
/// intact — can use `test(:name) do ... end` without the macro being spliced
/// into its text or added to the global Kernel bootstrap.
fn load_test_root_from_text(
    tel: ConfiguredTelemetry,
    source_name: String,
    text: String,
    module_name: Option<String>,
    name: String,
    arity: usize,
    diagnostic_status: &DiagnosticStatus,
) -> (Compiler2<ConfiguredTelemetry>, RootId) {
    let mut compiler = Compiler2::new(tel);
    DiagRenderer::new_to_stderr_with_status(
        compiler.source_map(),
        diagnostic_color_mode(),
        diagnostic_status.clone(),
    )
    .install(compiler.telemetry());
    compiler.set_drive_timeout(FZ2_COMPILER_DRIVE_TIMEOUT);
    compiler.submit_scoped_prelude(CodeSubmission {
        name: Some(TEST_MACRO_PRELUDE_NAME.to_string()),
        text: TEST_MACRO_PRELUDE_SOURCE.to_string(),
    });
    compiler.submit_code(CodeSubmission {
        name: Some(source_name),
        text,
    });
    let root = compiler.submit_root(RootSubmission {
        module_name,
        name,
        arity,
        need: ExecutableNeed::Value,
    });
    (compiler, root)
}

fn diagnostic_color_mode() -> ColorMode {
    if std::env::var_os("NO_COLOR").is_some() {
        ColorMode::Never
    } else {
        ColorMode::Auto
    }
}

#[cfg(test)]
mod discover_tests_test {
    use super::discover_tests;
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
    use super::{ScopeForm, TEST_MACRO_PRELUDE_NAME, TEST_MACRO_PRELUDE_SOURCE};
    use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
    use crate::telemetry::ConfiguredTelemetry;

    #[test]
    fn user_test_source_keeps_its_true_on_disk_span_offsets() {
        // The `test` item macro is supplied as a scoped prelude (its own
        // CodeId), never spliced into the user's source, so a node parsed from
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
        let user_text = "fn helper(x), do: x\n\ntest(:my_test) do\n  assert(helper(1) == 1)\nend\n".to_string();
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
                        .ast_node()
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
            test_form.span.code_id.0,
            user_code.as_u32(),
            "the user node's span must name the user's own code unit, not a combined prelude+user buffer"
        );
    }
}

#[cfg(test)]
mod requested_output_test {
    use super::*;

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
            text: "fn main(), do: 0\n".to_string(),
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
