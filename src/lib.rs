mod aot_link;
mod ast;
mod callsite_walk;
mod compiler;
mod diag;
mod dispatch_matrix;
mod frontend;
mod fz_ir;
mod ir_capture_norm;
mod ir_codegen;
mod ir_dest;
mod ir_extern_marshal;
mod ir_interp;
// ir_liveness removed (fz-ul4.11.31 subsumes .11.30): frame schemas are
// uniformly `[cont_ptr, ...entry_params]` with every Var slot as an opaque value ref;
// Cranelift handles temporary spills. The richer per-call liveness was
// never wired into codegen and the .11.31 root walker reads the existing
// schema directly. See fz-ul4.11.30 (subsumed).
mod cli;
mod exec;
mod ir_dce;
mod ir_fold;
mod ir_fuse;
mod ir_lower;
mod ir_planner;
mod modules;
mod parser;
mod specs;
mod telemetry;
#[cfg(test)]
mod test_support;
mod type_expr;
mod type_infer;
pub mod types;
use cli::repl::run_script;
use compiler::source::{FileId, SourceMap, Span};
use compiler::{Compiler, World};
use diag::{Diagnostic, codes::LOWER_UNBOUND, report_or_exit_through};
use exec::runtime::Runtime;
use frontend::{FrontendOk, FrontendResult};
use fz_ir::{FnCategory, FnId, FnIr, Module, SpecId};
use ir_codegen::{
    CompiledImage, CompiledProgram, asm_record_enable, asm_record_take, ir_text_record_enable, ir_text_record_take,
};
use ir_interp::run_main_with_plan;
use ir_planner::{
    fn_types::{SpecKey, display_return_demand},
    materialize_program, pretty_module_plan,
};
use libc::{c_int, close, write};
use modules::interface::{render_interfaces, validate_public_export_specs};
use modules::pipeline::{CompileMode, PipelineError, link_error_diagnostic};
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs::{self, read_to_string, remove_file};
use std::io::{IsTerminal, Read, stdin};
use std::path::{Path, PathBuf};
use std::process::{Command, exit};
use std::rc::Rc;
use telemetry::{
    ConfiguredTelemetry, DiagRenderer, Event, Handler, JsonlBackend, StatsHandler, Telemetry, next_compile_nonce,
};
use types::{DefaultTypes, KeySlot, display_key_slots};

const FZ_EXEC_READY_FD_ENV: &str = "FZ_EXEC_READY_FD";

pub(crate) fn notify_fixture_execution_start() {
    let Ok(raw_fd) = std::env::var(FZ_EXEC_READY_FD_ENV) else {
        return;
    };
    let Ok(fd) = raw_fd.parse::<c_int>() else {
        return;
    };
    let byte = [1_u8];
    unsafe {
        let _ = write(fd, byte.as_ptr().cast(), byte.len());
        let _ = close(fd);
    }
}

pub fn run() {
    let raw_args: Vec<String> = std::env::args().skip(1).collect();

    // Pre-scan global flags before subcommand dispatch. Strip them from the
    // args passed to subcommands so subcommand parsers never see them.
    let mut log_telemetry: Option<String> = None;
    let mut emit_stats = false;
    let mut args: Vec<String> = Vec::new();
    let mut i = 0;
    while i < raw_args.len() {
        match raw_args[i].as_str() {
            "--log-telemetry" => {
                i += 1;
                if let Some(v) = raw_args.get(i) {
                    log_telemetry = Some(v.clone());
                } else {
                    eprintln!("--log-telemetry expects a path");
                    exit(2);
                }
            }
            "--emit=stats" => {
                emit_stats = true;
            }
            a => args.push(a.to_string()),
        }
        i += 1;
    }

    let tel = ConfiguredTelemetry::new();
    if let Some(ref path) = log_telemetry {
        match JsonlBackend::new_file(Path::new(path)) {
            Ok(backend) => {
                tel.attach(&[], Box::new(backend));
            }
            Err(e) => {
                eprintln!("--log-telemetry {}: {}", path, e);
                exit(2);
            }
        }
    }
    let stats_handler = if emit_stats {
        let s = StatsHandler::new();
        tel.attach(&[], s.handler());
        Some(s)
    } else {
        None
    };

    match args.first().map(String::as_str) {
        Some("help" | "--help" | "-h") => {
            print_help();
        }
        Some("build") => {
            run_build(&tel, &args[1..]);
        }
        Some("run") => {
            run_jit_from_path(&tel, &args[1..]);
        }
        Some("dump") => {
            run_dump(&tel, &args[1..]);
        }
        Some("interp") => {
            run_interp(&tel, &args[1..]);
        }
        Some("repl") => {
            // fz-i67.1 — `--script <path>` drives the REPL non-interactively
            // for the fixture matrix's `repl` parity leg.
            if args.get(1).map(|s| s.as_str()) == Some("--script") {
                let path = args.get(2).cloned().unwrap_or_else(|| {
                    eprintln!("fz repl --script <path>");
                    exit(2);
                });
                if let Err(e) = run_script(Path::new(&path), &tel) {
                    eprintln!("repl: {}", e);
                    exit(1);
                }
            } else if let Err(e) = cli::repl::run() {
                eprintln!("repl: {}", e);
                exit(1);
            }
        }
        Some("test") => {
            let src = args.get(1).cloned().unwrap_or_else(|| {
                eprintln!("fz test <path>");
                exit(2);
            });
            if let Err(e) = cli::test_runner::run(Path::new(&src)) {
                eprintln!("{}", e);
                exit(1);
            }
        }
        _ => {
            // No subcommand. Two routes:
            //
            //   - Stdin is a TTY:  open the REPL (interactive use).
            //   - Stdin is a pipe / redirect:  read the program from stdin and run
            //     it through the JIT.
            //
            // No-argument SAMPLE-as-default is gone (was useful as a smoke test
            // during early language work; obsolete now that fixtures + `fz test`
            // + `fz run <path>` exist).
            if stdin().is_terminal() {
                if let Err(e) = cli::repl::run() {
                    eprintln!("repl: {}", e);
                    exit(1);
                }
            } else {
                let mut src = String::new();
                if let Err(e) = stdin().read_to_string(&mut src) {
                    eprintln!("reading stdin: {}", e);
                    exit(1);
                }
                run_jit_src(&tel, src, "<stdin>".into(), CompileMode::Normal);
            }
        }
    }

    if let Some(s) = stats_handler {
        s.print_summary();
    }
}

/// `fz build <src.fz> -o <out>` — AOT compile + link into a native
/// executable (fz-ul4.23.6.3).
///
/// Pipeline: lex/parse/resolve/macros/ir_lower (shared with `fz run`),
/// then `ir_codegen::compile_aot` to emit object bytes including the
/// per-program dispatch fn and a C-callable `main` that calls
/// `fz_aot_run_main` (in the fz-runtime staticlib). Then `cc` links the
/// object against libfz_runtime.a + libc into the requested output.
///
/// Single-task v1 — spawn/send/receive in AOT lands in fz-ul4.23.6.6.
struct ConsoleBuildHandler;

impl Handler for ConsoleBuildHandler {
    fn handle(&self, ev: &Event<'_, '_, '_>) {
        use telemetry::Value;
        let s = |k: &str| -> String {
            match ev.metadata.get(k) {
                Some(Value::Str(s)) => s.to_string(),
                _ => String::new(),
            }
        };
        match ev.name {
            n if n == ["fz", "build", "no_main"] => {
                eprintln!("fz build: no `main/0` fn found; nothing to link.");
            }
            n if n == ["fz", "build", "write_obj_failed"] => {
                eprintln!("write object {}: {}", s("path"), s("error"));
            }
            n if n == ["fz", "build", "cc_failed"] => {
                eprintln!("fz build: failed to invoke cc: {}", s("error"));
            }
            n if n == ["fz", "build", "cc_exit"] => {
                eprintln!("fz build: cc exited {}", s("status"));
            }
            n if n == ["fz", "build", "runtime_archive_failed"] => {
                eprintln!("fz build: runtime archive: {}", s("error"));
            }
            // linking / linked are silent at default verbosity — the
            // build subcommand has historically been silent on success.
            _ => {}
        }
    }
}

/// `fz help` / `fz --help` / `fz -h` — a brief tour of the commands and the
/// switches each accepts. Kept in lockstep with the subcommand parsers in this
/// file and the dump `--emit` set in `run_dump`.
fn print_help() {
    print!(
        "\
fz — the fz compiler and runtime

Usage:
  fz <command> [options] <src.fz>
  fz [options] < program.fz      read a program from stdin and JIT-run it
  fz                             start the REPL (when stdin is a terminal)

Commands:
  run     <src.fz>   JIT-compile and run a program
  build   <src.fz>   AOT-compile and link a native executable (needs -o)
  interp  <src.fz>   run through the IR interpreter
  dump    <src.fz>   inspect compiler output (CLIF, asm, specs, …)
  test    <src.fz>   compile and run the program's tests
  repl               start an interactive REPL
  help               show this help (also --help, -h)

Global options (placed before the command):
  --log-telemetry <path>   append JSONL telemetry events to <path>
  --emit=stats             print a stats summary on exit

Compile options (run, build, dump):
  --lto, --whole-program   whole-program mode: erase module boundaries

build options:
  -o <out>                 output executable path (required)

dump options:
  --emit <what>            clif | asm | both | interfaces | specs |
                           bodies | outcomes | stats   (default: clif)
  --fn <name>              restrict a clif/asm dump to one function
  --all                    include prelude / dead bodies (with --emit outcomes)
  --strict-interfaces      validate public export specs (with --emit interfaces)

repl options:
  --script <path>          run a REPL script non-interactively
"
    );
}

fn run_build(tel: &dyn Telemetry, args: &[String]) {
    let sm_cell: Rc<RefCell<SourceMap>> = Rc::new(RefCell::new(SourceMap::new()));
    tel.attach(&["fz", "diag"], Box::new(DiagRenderer::new_stderr(sm_cell.clone())));
    tel.attach(&["fz", "build"], Box::new(ConsoleBuildHandler));

    let mut compiler = Compiler::new();
    let mut src_path: Option<String> = None;
    let mut out_path: Option<String> = None;
    let mut mode = CompileMode::Normal;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--lto" | "--whole-program" => mode = CompileMode::Lto,
            "-o" => {
                i += 1;
                out_path = args.get(i).cloned();
                if out_path.is_none() {
                    eprintln!("fz build: -o expects a path");
                    exit(2);
                }
            }
            a if !a.starts_with('-') && src_path.is_none() => {
                src_path = Some(a.to_string());
            }
            a => {
                eprintln!("fz build: unknown arg `{}`", a);
                exit(2);
            }
        }
        i += 1;
    }
    let src_path = src_path.unwrap_or_else(|| {
        eprintln!("fz build [--lto] <src.fz> -o <out>");
        exit(2);
    });
    let out_path = out_path.unwrap_or_else(|| {
        eprintln!("fz build: -o <out> is required");
        exit(2);
    });
    let src = read_to_string(&src_path).unwrap_or_else(|e| {
        eprintln!("read {}: {}", src_path, e);
        exit(1);
    });

    let mut world = World::new();
    compiler
        .prepare_execution_graph_from_source(&mut world, src, src_path.clone(), tel, mode)
        .unwrap_or_else(|err| report_pipeline_error_or_exit("fz build", tel, &sm_cell, err));
    *sm_cell.borrow_mut() = world.sm().clone();
    report_or_exit_through(tel, world.diagnostics().as_slice());

    let obj_name = Path::new(&src_path)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("fz_program");
    let artifact = compiler
        .compile_aot_planned(&mut world, obj_name, tel)
        .unwrap_or_else(|e| {
            report_or_exit_through(tel, &[e.to_diagnostic()]);
            exit(1);
        });

    if artifact.main_symbol.is_none() {
        tel.emit(&["fz", "build", "no_main"]);
        exit(1);
    }
    // fz-d5b — gate on errors. `collect_diagnostics` emits Severity::Error
    // for soundness leaks (TYPE_OPAQUE_VISIBILITY, TYPE_OPAQUE_ARITHMETIC,
    // TYPE_IMPURE_RECEIVE_GUARD); before this gate they rendered but the
    // build continued, masking the rejection.
    report_or_exit_through(tel, artifact.diagnostics.as_slice());

    // Write the object next to the output, then invoke cc.
    let obj_temp = PathBuf::from(format!("{}.o", out_path));
    fs::write(&obj_temp, &artifact.object).unwrap_or_else(|e| {
        tel.event(
            &["fz", "build", "write_obj_failed"],
            metadata! { path: obj_temp.display().to_string(), error: e.to_string() },
        );
        exit(1);
    });

    let runtime_archive = aot_link::resolve_runtime_archive().unwrap_or_else(|e| {
        tel.event(
            &["fz", "build", "runtime_archive_failed"],
            metadata! { error: e.to_string() },
        );
        exit(1);
    });

    let mut cc = Command::new("cc");
    cc.arg("-o").arg(&out_path).arg(&obj_temp).arg(&runtime_archive.path);
    if cfg!(target_os = "macos") {
        cc.arg("-Wl,-undefined,dynamic_lookup");
    }
    tel.event(
        &["fz", "build", "linking"],
        metadata! {
            output: out_path.clone(),
            runtime_archive: runtime_archive.path.display().to_string(),
            runtime_archive_source: runtime_archive.source.as_str(),
        },
    );
    let status = cc.status().unwrap_or_else(|e| {
        tel.event(&["fz", "build", "cc_failed"], metadata! { error: e.to_string() });
        exit(1);
    });
    if !status.success() {
        tel.event(&["fz", "build", "cc_exit"], metadata! { status: status.to_string() });
        exit(1);
    }
    tel.event(&["fz", "build", "linked"], metadata! { output: out_path.clone() });
    // Drop the intermediate .o on success.
    let _ = remove_file(&obj_temp);
}

/// `fz interp <src.fz>` — run a program through the rebuilt IR interpreter
/// (ir_interp). The interp walks Module directly using the same
/// tagged-ref rep, heap, and runtime FFI as the JIT.
///
/// Coverage grows feature-by-feature across fz-ul4.23.5.2 → .5.8. If the
/// interp hits an IR construct it doesn't yet support, it returns a
/// "not yet supported" error and exits 75 (EX_TEMPFAIL) so the fixture
/// matrix logs the path as Deferred rather than failing.
fn run_interp(tel: &dyn Telemetry, args: &[String]) {
    let sm_cell: Rc<RefCell<SourceMap>> = Rc::new(RefCell::new(SourceMap::new()));
    tel.attach(&["fz", "diag"], Box::new(DiagRenderer::new_stderr(sm_cell.clone())));

    let mut compiler = Compiler::new();
    let path = args.first().cloned().unwrap_or_else(|| {
        eprintln!("fz interp <src.fz>");
        exit(2);
    });
    let src = read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("read {}: {}", path, e);
        exit(1);
    });
    let mut world = World::new();
    compiler
        .prepare_execution_graph_from_source(&mut world, src, path, tel, CompileMode::Normal)
        .unwrap_or_else(|err| report_pipeline_error_or_exit("fz interp", tel, &sm_cell, err));
    *sm_cell.borrow_mut() = world.sm().clone();
    report_or_exit_through(tel, world.diagnostics().as_slice());
    notify_fixture_execution_start();
    let module = world.linked_module().clone();
    let module_plan = world.linked_module_plan().clone();
    match run_main_with_plan(world.types(), tel, &module, module_plan) {
        Ok(_halt) => {}
        Err(msg) => {
            eprintln!("fz interp: {}", msg);
            // Treat "not yet supported" errors as graceful Deferred so the
            // matrix can roll out interp coverage incrementally.
            if msg.contains("not yet supported") {
                exit(75);
            }
            exit(1);
        }
    }
}

fn run_jit_from_path(tel: &dyn Telemetry, args: &[String]) {
    let mut mode = CompileMode::Normal;
    let mut src_path: Option<String> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--lto" | "--whole-program" => mode = CompileMode::Lto,
            a if !a.starts_with("--") && src_path.is_none() => src_path = Some(a.to_string()),
            a => {
                eprintln!("fz run: unknown arg `{}`", a);
                exit(2);
            }
        }
        i += 1;
    }
    let src_path = src_path.unwrap_or_else(|| {
        eprintln!("fz run [--lto] <src.fz>");
        exit(2);
    });
    let src = read_to_string(&src_path).unwrap_or_else(|e| {
        eprintln!("read {}: {}", src_path, e);
        exit(1);
    });
    run_jit_src(tel, src, src_path, mode);
}

/// `fz dump <src.fz> [--emit clif|asm|both] [--fn <name>]` — drive a
/// source file through the full JIT pipeline up to (but not including)
/// final fn-ptr resolution, capture per-fn Cranelift IR text and/or
/// post-regalloc machine-code disassembly, and print to stdout. The
/// program is NOT executed.
///
/// Feedback-loop tooling: fz-ul4.23.3 (clif), fz-ul4.23.7 (srcloc),
/// fz-ul4.23.8 (asm + --emit both).
/// Re-emit a Cranelift IR dump in our own layout. Cranelift reserves a
/// wide left gutter for `@<hex>` srclocs, which leaves unannotated lines
/// pushed far right and annotated lines pinned at col 0 — the mismatch
/// is hard to read. We strip the gutter, re-indent from scratch, decode
/// the srcloc to `@line:col`, and fold it into a trailing comment on
/// each inst. Srcloc encoding (top 8 bits = file_id, low 24 bits =
/// byte offset) matches `span_to_srcloc` in src/ir_codegen.rs.
fn format_clif(text: &str, sm: &SourceMap) -> String {
    const BODY_WIDTH: usize = 40;
    let mut out = String::with_capacity(text.len() + 64);
    for line in text.lines() {
        let trimmed = line.trim_start();
        if trimmed.is_empty() {
            out.push('\n');
            continue;
        }

        // Peel an optional `@<hex>` srcloc prefix off the front.
        let (srcloc, rest) = if let Some(after_at) = trimmed.strip_prefix('@') {
            let (hex, tail) = after_at.split_at(after_at.find(' ').unwrap_or(after_at.len()));
            match u32::from_str_radix(hex, 16) {
                Ok(bits) => {
                    let file_id = FileId(bits >> 24);
                    let offset = bits & 0x00FF_FFFF;
                    if (file_id.0 as usize) < sm.file_count() {
                        let loc = sm.locate(Span::new(file_id, offset, offset));
                        (Some(format!("{}:{}", loc.line, loc.col)), tail.trim_start())
                    } else {
                        (None, trimmed)
                    }
                }
                Err(_) => (None, trimmed),
            }
        } else {
            (None, trimmed)
        };

        // Classify and pick indent. Function header and closing brace at
        // col 0; block headers at col 0 within the function; everything
        // else (sig/fn/gv decls, instructions) at col 4.
        let is_top = rest.starts_with("function ") || rest == "}";
        let is_block_header = rest.starts_with("block") && rest.trim_end().ends_with(':');
        let indent = if is_top || is_block_header { "" } else { "    " };

        if let Some(loc) = srcloc {
            // Merge srcloc into any existing `; ...` const-prop hint so we
            // end up with one comment block: `<body>  ; @L:C  <hint>`.
            let (body, hint) = match rest.find(';') {
                Some(idx) => {
                    let (b, h) = rest.split_at(idx);
                    (b.trim_end(), h.trim_start_matches(';').trim())
                }
                None => (rest, ""),
            };
            let body_line = format!("{}{}", indent, body);
            let pad = BODY_WIDTH.saturating_sub(body_line.len());
            out.push_str(&body_line);
            for _ in 0..pad.max(1) {
                out.push(' ');
            }
            if hint.is_empty() {
                out.push_str(&format!("; @{}\n", loc));
            } else {
                out.push_str(&format!("; @{}  {}\n", loc, hint));
            }
        } else {
            out.push_str(indent);
            out.push_str(rest);
            out.push('\n');
        }
    }
    out
}

struct ConsoleDumpHandler;

impl Handler for ConsoleDumpHandler {
    fn handle(&self, ev: &Event<'_, '_, '_>) {
        use telemetry::Value;
        let text = |key: &str| -> Option<String> {
            match ev.metadata.get(key) {
                Some(Value::Str(s)) => Some(s.to_string()),
                _ => None,
            }
        };
        match ev.name {
            n if n == ["fz", "dump", "fn_header"] => {
                if let Some(name) = text("name") {
                    println!("; fn {}", name);
                }
            }
            n if n == ["fz", "dump", "clif"] => {
                if let Some(s) = text("text") {
                    println!("{}", s);
                }
            }
            n if n == ["fz", "dump", "asm_separator"] => {
                println!("; ---- asm ----");
            }
            n if n == ["fz", "dump", "asm"] => {
                if let Some(s) = text("text") {
                    println!("{}", s);
                }
            }
            n if n == ["fz", "dump", "specs"]
                || n == ["fz", "dump", "interfaces"]
                || n == ["fz", "dump", "bodies"]
                || n == ["fz", "dump", "outcomes"] =>
            {
                if let Some(s) = text("text") {
                    print!("{}", s);
                }
            }
            n if n == ["fz", "dump", "no_fn_match"] => {
                let filter = text("filter").unwrap_or_default();
                let avail = text("available").unwrap_or_default();
                eprintln!("fz dump: no fn named `{}` (available: {})", filter, avail);
            }
            _ => {}
        }
    }
}

fn run_dump(tel: &dyn Telemetry, args: &[String]) {
    let sm_cell: Rc<RefCell<SourceMap>> = Rc::new(RefCell::new(SourceMap::new()));
    tel.attach(&["fz", "diag"], Box::new(DiagRenderer::new_stderr(sm_cell.clone())));
    tel.attach(&["fz", "dump"], Box::new(ConsoleDumpHandler));

    let mut path: Option<String> = None;
    let mut fn_filter: Option<String> = None;
    let mut emit = "clif".to_string();
    let mut show_all = false;
    let mut strict_interfaces = false;
    let mut mode = CompileMode::Normal;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--emit" => {
                i += 1;
                emit = args.get(i).cloned().unwrap_or_else(|| {
                    eprintln!("fz dump: --emit expects a value (clif)");
                    exit(2);
                });
            }
            "--fn" => {
                i += 1;
                fn_filter = args.get(i).cloned();
                if fn_filter.is_none() {
                    eprintln!("fz dump: --fn expects a name");
                    exit(2);
                }
            }
            // fz-f88.7 — bypass dump_outcomes filtering (prelude + dead bodies).
            "--all" => show_all = true,
            "--strict-interfaces" => strict_interfaces = true,
            "--lto" | "--whole-program" => mode = CompileMode::Lto,
            a if !a.starts_with("--") && path.is_none() => path = Some(a.to_string()),
            a => {
                eprintln!("fz dump: unknown arg `{}`", a);
                exit(2);
            }
        }
        i += 1;
    }
    let path = path.unwrap_or_else(|| {
        eprintln!(
            "fz dump <src.fz> [--lto] [--emit clif|asm|both|interfaces|specs|bodies|outcomes|stats] [--fn <name>]"
        );
        exit(2);
    });
    let emit_clif = matches!(emit.as_str(), "clif" | "both");
    let emit_asm = matches!(emit.as_str(), "asm" | "both");
    let emit_specs = emit.as_str() == "specs";
    let emit_interfaces = matches!(emit.as_str(), "interface" | "interfaces");
    let emit_stats = emit.as_str() == "stats";
    // fz-jg5.8 (RED.7) — user-facing diagnostic: list every emitted body
    // and (in v1) its source spec key. Boundary attribution per-call is a
    // follow-on; this v1 prints the spec set and a single-line summary so
    // the user can see "0 user fns" for programs with no surviving user
    // functions in the plan.
    let emit_bodies = emit.as_str() == "bodies";
    // fz-9pr.16 — `outcomes`: per-callsite planner verdict diary.
    let emit_outcomes = emit.as_str() == "outcomes";
    if !emit_clif && !emit_asm && !emit_specs && !emit_interfaces && !emit_bodies && !emit_outcomes && !emit_stats {
        eprintln!(
            "fz dump: --emit must be one of `clif`, `asm`, `both`, `interfaces`, `specs`, `bodies`, `outcomes`, `stats`"
        );
        exit(2);
    }
    let src = read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("read {}: {}", path, e);
        exit(1);
    });
    let mut compiler = Compiler::new();

    if emit_specs {
        if fn_filter.is_some() {
            eprintln!("fz dump: --fn is ignored with --emit specs (spec dump is per-module)");
        }
        let dump = dump_specs_pipeline(&mut compiler, tel, &sm_cell, src, path.clone());
        tel.event(&["fz", "dump", "specs"], metadata! { text: dump });
        return;
    }

    if emit_interfaces {
        if fn_filter.is_some() {
            eprintln!("fz dump: --fn is ignored with --emit interfaces");
        }
        let dump = dump_interfaces_pipeline(&mut compiler, tel, &sm_cell, src, path.clone(), strict_interfaces);
        tel.event(&["fz", "dump", "interfaces"], metadata! { text: dump });
        return;
    }

    if emit_bodies {
        if fn_filter.is_some() {
            eprintln!("fz dump: --fn is ignored with --emit bodies");
        }
        tel.event(
            &["fz", "dump", "bodies"],
            metadata! { text: dump_bodies_pipeline(&mut compiler, tel, &sm_cell, src, path.clone(), mode) },
        );
        return;
    }

    if emit_outcomes {
        if fn_filter.is_some() {
            eprintln!("fz dump: --fn is ignored with --emit outcomes");
        }
        tel.event(
            &["fz", "dump", "outcomes"],
            metadata! {
                text: dump_outcomes_pipeline(&mut compiler, tel, &sm_cell, src, path.clone(), show_all, mode)
            },
        );
        return;
    }

    if emit_stats {
        if fn_filter.is_some() {
            eprintln!("fz dump: --fn is ignored with --emit stats");
        }
        let _ = compile_pipeline(&mut compiler, tel, &sm_cell, src, path.clone(), mode);
        return;
    }

    if emit_clif {
        ir_text_record_enable();
    }
    if emit_asm {
        asm_record_enable();
    }
    let compiled = compile_pipeline(&mut compiler, tel, &sm_cell, src, path.clone(), mode);
    let clif_entries = if emit_clif { ir_text_record_take() } else { Vec::new() };
    let asm_entries = if emit_asm { asm_record_take() } else { Vec::new() };

    // Combine into a single fn-name → (clif?, asm?) map preserving order.
    let mut order: Vec<String> = Vec::new();
    let mut clif_map: HashMap<String, String> = HashMap::new();
    let mut asm_map: HashMap<String, String> = HashMap::new();
    for (name, text) in &clif_entries {
        if !clif_map.contains_key(name) {
            order.push(name.clone());
        }
        clif_map.insert(name.clone(), text.clone());
    }
    for (name, text) in &asm_entries {
        if !clif_map.contains_key(name) && !asm_map.contains_key(name) {
            order.push(name.clone());
        }
        asm_map.insert(name.clone(), text.clone());
    }

    let mut printed = 0usize;
    for name in &order {
        if let Some(filter) = &fn_filter {
            // fz-ul4.29.7: narrow specs print as `<fn>_s<spec_id>`; match
            // both the bare name and any `<name>_s*` variants when the
            // user filters on `<name>`.
            let suffix_match = name.starts_with(filter.as_str()) && name[filter.len()..].starts_with("_s");
            if name != filter && !suffix_match {
                continue;
            }
        }
        tel.event(&["fz", "dump", "fn_header"], metadata! { name: name.clone() });
        if emit_clif && let Some(text) = clif_map.get(name) {
            tel.event(
                &["fz", "dump", "clif"],
                metadata! { text: format_clif(text, &compiled.sm) },
            );
        }
        if emit_asm && let Some(text) = asm_map.get(name) {
            if emit_clif {
                tel.emit(&["fz", "dump", "asm_separator"]);
            }
            tel.event(&["fz", "dump", "asm"], metadata! { text: text.clone() });
        }
        printed += 1;
    }
    if let Some(filter) = &fn_filter
        && printed == 0
    {
        tel.event(
            &["fz", "dump", "no_fn_match"],
            metadata! { filter: filter.clone(), available: order.join(", ") },
        );
        exit(1);
    }
}

/// Run the frontend pipeline, updating `sm_cell` and routing diagnostics
/// through the bus. Exits(1) on error or on any `Severity::Error` diagnostic.
fn run_frontend(result: FrontendResult, sm_cell: &Rc<RefCell<SourceMap>>, tel: &dyn Telemetry) -> FrontendOk {
    let ok = result.unwrap_or_else(|err| {
        *sm_cell.borrow_mut() = err.sm;
        report_or_exit_through(tel, err.diagnostics.as_slice());
        exit(1);
    });
    *sm_cell.borrow_mut() = ok.sm.clone();
    report_or_exit_through(tel, ok.diagnostics.as_slice());
    ok
}

/// Drive a source string through the lex → parse → resolve → macros →
/// ir_lower → ir_codegen stages. Returns the compiled module; callers
/// either execute (`fz run`) or inspect (`fz dump`).
///
/// Single render path: every error from every stage goes through
/// diag::render_to_stderr. Lex / parse errors carry proper spans; later-
/// stage errors carry the spans threaded in by fz-ul4.20 / .21.
struct Compiled {
    image: CompiledImage,
    main_fn: Option<FnId>,
    /// SourceMap surfaced so `fz dump` can resolve Cranelift's `@<hex>`
    /// srclocs back to `file:line:col`. fz-ul4.23.7.
    sm: SourceMap,
    /// fz-swt.10 — IR Module kept alive past codegen so the runtime's
    /// `MakeResourceHook` thunk can walk dtor closure bodies.
    module: Module,
}

fn report_pipeline_error_or_exit(
    context: &str,
    tel: &dyn Telemetry,
    sm_cell: &Rc<RefCell<SourceMap>>,
    err: PipelineError,
) -> ! {
    let _ = sm_cell;
    match err {
        PipelineError::Link(err) => {
            let diagnostic = link_error_diagnostic(err);
            report_or_exit_through(tel, &[diagnostic]);
        }
        err => {
            if !err.diagnostics_emitted() {
                eprintln!("{context}: {err}");
            }
        }
    }
    exit(1);
}

/// fz-73m — drive a source string through lex → parse → resolve → macros
/// → ir_lower → plan_module_with_role, then pretty-print `ModulePlan` for golden
/// inspection. Skips codegen entirely; the dump is a planner-only view.
fn dump_specs_pipeline(
    compiler: &mut Compiler,
    tel: &dyn Telemetry,
    sm_cell: &Rc<RefCell<SourceMap>>,
    src: String,
    source_name: String,
) -> String {
    let mut world = World::new();
    let frontend = run_frontend(compiler.compile_source(&mut world, src, source_name, tel), sm_cell, tel);
    pretty_module_plan(world.types(), &frontend.module, &frontend.module_plan)
}

fn dump_interfaces_pipeline(
    compiler: &mut Compiler,
    tel: &dyn Telemetry,
    sm_cell: &Rc<RefCell<SourceMap>>,
    src: String,
    source_name: String,
    strict: bool,
) -> String {
    let mut world = World::new();
    let frontend = run_frontend(compiler.compile_source(&mut world, src, source_name, tel), sm_cell, tel);
    if strict {
        let diags = validate_public_export_specs(&frontend._prog.module_interfaces);
        report_or_exit_through(tel, &diags);
    }
    render_interfaces(&frontend._prog.module_interfaces)
}

fn render_key_slots(t: &mut DefaultTypes, key: &[KeySlot]) -> String {
    display_key_slots(t, key)
}

fn render_spec_key(t: &mut DefaultTypes, spec_key: &SpecKey) -> String {
    format!(
        "{} demand={}",
        render_key_slots(t, &spec_key.input),
        display_return_demand(t, &spec_key.demand)
    )
}

fn render_dispatch_target<F: Fn(FnId) -> String>(t: &mut DefaultTypes, fn_name: &F, target: &SpecKey) -> String {
    format!(
        "{}#{} {}",
        fn_name(target.fn_id),
        target.fn_id.0,
        render_spec_key(t, target)
    )
}

/// fz-jg5.8 (RED.7) — `fz dump --emit bodies`: print every user fn that
/// survives planning with the spec keys codegen emits for it. A program
/// with no surviving user functions shows `bodies emitted: 0 user
/// functions (no user functions in the plan)`.
///
/// Each entry is `<fn_name>: <N> spec(s) [<key_1>] [<key_2>] ...`. The
/// dump runs the compile pipeline through `plan_module_with_role`; the surviving
/// fns and their spec keys are read out of `ModulePlan`.
fn dump_bodies_pipeline(
    compiler: &mut Compiler,
    tel: &dyn Telemetry,
    sm_cell: &Rc<RefCell<SourceMap>>,
    src: String,
    source_name: String,
    mode: CompileMode,
) -> String {
    use crate::telemetry::TelemetryExt as _;
    let mut world = World::new();
    compiler
        .prepare_execution_graph_from_source(&mut world, src, source_name, tel, mode)
        .unwrap_or_else(|err| report_pipeline_error_or_exit("fz dump", tel, sm_cell, err));
    *sm_cell.borrow_mut() = world.sm().clone();
    report_or_exit_through(tel, world.diagnostics().as_slice());
    let module = world.linked_module().clone();
    let module_plan = world.linked_module_plan().clone();
    let _compile_span = tel.span(
        &["fz", "compile"],
        crate::metadata! {
            compile_nonce: next_compile_nonce(),
            module_path: module.module_path().to_owned(),
        },
    );
    let planned_program = materialize_program(world.types(), &module, &module_plan, tel);

    // Group surviving specs by user-fn name. Skip the conventional
    // synthetic helpers (k_*, fn_clause_*, lambda_*) — they're
    // continuations or pattern-clause bodies, not user fns.
    let mut by_name: BTreeMap<String, Vec<SpecKey>> = BTreeMap::new();
    for sid in planned_program.reachable_specs() {
        let planned_body = planned_program.executable_body(SpecId(*sid));
        let name = &planned_body.body.name;
        if name.starts_with("k_") || name.starts_with("fn_clause_") || name.starts_with("lambda_") || name == "main" {
            continue;
        }
        by_name
            .entry(name.clone())
            .or_default()
            .push(planned_body.spec_key.clone());
    }

    let mut out = String::new();
    if by_name.is_empty() {
        out.push_str("bodies emitted: 0 user functions\n");
        out.push_str("  (no user functions in the plan)\n");
        return out;
    }
    for keys in by_name.values_mut() {
        keys.sort_by(|a, b| format!("{:?}", a).cmp(&format!("{:?}", b)));
    }
    out.push_str(&format!(
        "bodies emitted: {} user function{}\n",
        by_name.len(),
        if by_name.len() == 1 { "" } else { "s" }
    ));
    for (name, keys) in by_name {
        out.push_str(&format!(
            "  {}: {} spec{}\n",
            name,
            keys.len(),
            if keys.len() == 1 { "" } else { "s" }
        ));
        for key in keys {
            out.push_str(&format!("    {}\n", render_spec_key(world.types(), &key)));
        }
    }
    out
}

/// fz-9pr.16 — `fz dump --emit outcomes`: per-callsite verdict diary.
///
/// Runs the codegen front half (lex → parse → resolve → macros →
/// ir_lower → plan_module_with_role) and prints every call-edge entry in
/// `mt.specs[*].call_edges`, grouped by caller fn. Output shape:
///
/// ```text
/// outcomes for <source>
///
/// <caller_fn>:
///   blk<id> <slot> -> <verdict>[ (<target>)]
///   ...
/// ```
///
/// Use this to see how each callsite dispatches — every row shows the
/// resolved spec key (`Static` for Direct/Cont, `Indirect` for
/// ClosureCall).
///
/// fz-f88.7 — by default, two classes of caller are hidden so the
/// signal stays focused on user-program code:
///   - callers whose `FnIr.category == Prelude` (print noise
///     that's the same in every fixture);
///   - callers whose `FnId` has no reachable spec in the plan
///     (the body is dead-coded).
///
/// Pass `show_all=true` (CLI `--all`) to bypass both filters.
fn dump_outcomes_pipeline(
    compiler: &mut Compiler,
    tel: &dyn Telemetry,
    sm_cell: &Rc<RefCell<SourceMap>>,
    src: String,
    source_name: String,
    show_all: bool,
    mode: CompileMode,
) -> String {
    use crate::fz_ir::{CallsiteId, EmitSlot};
    use crate::telemetry::TelemetryExt as _;
    let mut world = World::new();
    compiler
        .prepare_execution_graph_from_source(&mut world, src, source_name.clone(), tel, mode)
        .unwrap_or_else(|err| report_pipeline_error_or_exit("fz dump", tel, sm_cell, err));
    *sm_cell.borrow_mut() = world.sm().clone();
    report_or_exit_through(tel, world.diagnostics().as_slice());
    let module = world.linked_module().clone();
    let _compile_span = tel.span(
        &["fz", "compile"],
        crate::metadata! {
            compile_nonce: next_compile_nonce(),
            module_path: module.module_path().to_owned(),
        },
    );
    let mt = ir_planner::plan_module_with_role(world.types(), &module, tel, "dump_outcomes");

    let fn_name = |fid: FnId| -> String {
        module
            .fns
            .iter()
            .find(|f| f.id == fid)
            .map(|f| f.name.clone())
            .unwrap_or_else(|| format!("?fn{}", fid.0))
    };

    let slot_str = |s: EmitSlot| -> &'static str {
        match s {
            EmitSlot::Direct => "Direct",
            EmitSlot::Cont => "Cont",
            EmitSlot::ClosureCall => "ClosureCall",
            EmitSlot::CallableBoundary => "CallableBoundary",
        }
    };
    let render_span = |sp: Span| -> String {
        if sp.is_dummy() {
            "<generated>".to_string()
        } else {
            format!("{}:{}-{}", sp.file.0, sp.start, sp.end)
        }
    };

    // fz-try.11 — rows are computed per (caller_spec) so section headers
    // can carry the spec inline (`apply1[α=int, β=int]:`) instead of the
    // pre-fz-try.11 `apply1:` + per-row `[under apply1[...]]` annotation.
    // The Outcome enum separates the structural slot (where) from the
    // demand-aware dispatch outcome (what).
    enum Outcome {
        Static(SpecKey),
        Indirect(SpecKey),
    }

    fn render_outcome<F: Fn(FnId) -> String>(t: &mut DefaultTypes, fn_name: &F, outcome: &Outcome) -> String {
        match outcome {
            Outcome::Static(target) => {
                format!("Static({})", render_dispatch_target(t, fn_name, target))
            }
            Outcome::Indirect(target) => {
                format!("Indirect({})", render_dispatch_target(t, fn_name, target))
            }
        }
    }

    // Rows grouped by (caller_fid, caller_key) → list of (cid, Dispatch).
    type Section = (SpecKey, Vec<(CallsiteId, Outcome)>);
    type SortKey = (u32, String);
    type RowsBySpec = BTreeMap<SortKey, Section>;
    let mut rows_by_spec: RowsBySpec = BTreeMap::new();

    let push_row = |rows_by_spec: &mut RowsBySpec,
                    caller_fid: FnId,
                    caller_key: &SpecKey,
                    cid: CallsiteId,
                    dispatch: Outcome,
                    sort_key: String| {
        let entry = rows_by_spec
            .entry((caller_fid.0, sort_key))
            .or_insert_with(|| (caller_key.clone(), Vec::new()));
        entry.1.push((cid, dispatch));
    };

    // Per-caller-spec dispatch rows (Static for Direct/Cont; Indirect for
    // ClosureCall).
    for (caller_key, ft) in &mt.specs {
        for (cid, edge) in ft.call_edges.iter() {
            let Some(target) = edge.local_target() else {
                continue;
            };
            let dispatch = match cid.slot {
                EmitSlot::ClosureCall => Outcome::Indirect(target.clone()),
                _ => Outcome::Static(target.clone()),
            };
            let sort_key = render_spec_key(world.types(), caller_key);
            push_row(
                &mut rows_by_spec,
                caller_key.fn_id,
                caller_key,
                cid.clone(),
                dispatch,
                sort_key,
            );
        }
    }

    // Stable per-section row ordering: span_start, then slot, then
    // serialized dispatch (deterministic across runs).
    for (_, rows) in rows_by_spec.values_mut() {
        rows.sort_by(|a, b| {
            a.0.ident
                .span()
                .start
                .cmp(&b.0.ident.span().start)
                .then_with(|| slot_str(a.0.slot).cmp(slot_str(b.0.slot)))
                .then_with(|| {
                    render_outcome(world.types(), &fn_name, &a.1).cmp(&render_outcome(world.types(), &fn_name, &b.1))
                })
        });
    }

    let mut out = String::new();
    out.push_str(&format!("outcomes for {}\n", source_name));
    if rows_by_spec.is_empty() {
        out.push_str("  (no callsites — program is callsite-free)\n");
        return out;
    }
    // fz-f88.7 — default filter: hide prelude callers and any caller
    // whose body has no surviving spec in the plan. `--all` bypasses.
    let reachable_fids: HashSet<FnId> = mt.specs.keys().map(|key| key.fn_id).collect();
    let should_show = |f: &FnIr| -> bool {
        if show_all {
            return true;
        }
        if f.category == FnCategory::Prelude {
            return false;
        }
        reachable_fids.contains(&f.id)
    };
    let module_fn_order: HashMap<FnId, usize> = module.fns.iter().enumerate().map(|(i, f)| (f.id, i)).collect();
    type SectionRef<'a> = (SortKey, &'a SpecKey, &'a Vec<(CallsiteId, Outcome)>);
    let mut sections: Vec<SectionRef<'_>> = rows_by_spec.iter().map(|(k, (sk, rs))| (k.clone(), sk, rs)).collect();
    sections.sort_by_key(|(k, _, _)| {
        (
            module_fn_order.get(&FnId(k.0)).copied().unwrap_or(usize::MAX),
            k.1.clone(),
        )
    });
    for (_, caller_key, rows) in sections {
        let Some(f) = module.fns.iter().find(|f| f.id == caller_key.fn_id) else {
            continue;
        };
        if !should_show(f) {
            continue;
        }
        // fz-try.11 — section header carries the caller spec inline.
        out.push_str(&format!(
            "\n{}{}:\n",
            f.name,
            render_spec_key(world.types(), caller_key)
        ));
        for (cid, dispatch) in rows {
            out.push_str(&format!(
                "  @{} {} -> {}\n",
                render_span(cid.ident.span()),
                slot_str(cid.slot),
                render_outcome(world.types(), &fn_name, dispatch),
            ));
        }
    }
    out
}

fn compile_pipeline(
    compiler: &mut Compiler,
    tel: &dyn Telemetry,
    sm_cell: &Rc<RefCell<SourceMap>>,
    src: String,
    source_name: String,
    mode: CompileMode,
) -> Compiled {
    let mut world = World::new();
    compiler
        .prepare_execution_graph_from_source(&mut world, src, source_name, tel, mode)
        .unwrap_or_else(|err| report_pipeline_error_or_exit("fz run", tel, sm_cell, err));
    *sm_cell.borrow_mut() = world.sm().clone();
    report_or_exit_through(tel, world.diagnostics().as_slice());
    let main_fn = world.linked_module().fn_by_name("main").map(|f| f.id);
    let executable = compiler.compile_planned(&mut world, tel).unwrap_or_else(|e| {
        report_or_exit_through(tel, &[e.to_diagnostic()]);
        exit(1);
    });
    tel.event(
        &["fz", "module", "unit_compiled"],
        metadata! {
            fns: world.linked_module().fns.len() as i64,
            atoms: world.linked_module().atom_names.len() as i64,
        },
    );
    // fz-d5b — gate on errors from the planner-side diagnostics
    // (TYPE_OPAQUE_VISIBILITY, TYPE_OPAQUE_ARITHMETIC,
    // TYPE_IMPURE_RECEIVE_GUARD). Severity::Warning entries print and
    // we continue; Severity::Error halts.
    report_or_exit_through(tel, executable.diagnostics().as_slice());
    let image = if world.units().len() == 1 {
        let unit = world.units()[0]
            .clone()
            .with_code_and_plan(world.linked_module().clone(), world.linked_module_plan().clone());
        CompiledProgram::new(unit, executable).link_image(tel)
    } else {
        Ok(CompiledImage::from_linked(tel, world.units().len(), executable))
    }
    .unwrap_or_else(|err| report_pipeline_error_or_exit("fz run", tel, sm_cell, PipelineError::Link(err)));
    if let Some(metadata) = image.metadata() {
        tel.event(
            &["fz", "link", "metadata"],
            metadata! {
                atoms: metadata.atoms.len() as i64,
                schemas: metadata.schemas.len() as i64,
                frames: metadata.frame_sizes.len() as i64,
                imports: metadata.imported_refs.len() as i64,
                exports: metadata.exported_symbols.len() as i64,
                static_closures: metadata.static_closures.len() as i64,
                halt_kinds: metadata.halt_kinds.len() as i64,
                relocations: metadata.relocations.len() as i64,
                has_resume: metadata.entrypoints.resume,
                has_main: metadata.entrypoints.main,
            },
        );
    }
    Compiled {
        image,
        main_fn,
        sm: world.sm().clone(),
        module: world.linked_module().clone(),
    }
}

/// `fz run <path>` (and the no-argument stdin route) — compile, then drive
/// the program through the Runtime so concurrency-using fixtures work
/// end-to-end.
fn run_jit_src(tel: &dyn Telemetry, src: String, source_name: String, mode: CompileMode) {
    let sm_cell: Rc<RefCell<SourceMap>> = Rc::new(RefCell::new(SourceMap::new()));
    tel.attach(&["fz", "diag"], Box::new(DiagRenderer::new_stderr(sm_cell.clone())));
    let mut compiler = Compiler::new();
    let compiled = compile_pipeline(&mut compiler, tel, &sm_cell, src, source_name, mode);
    let Some(main_fn) = compiled.main_fn else {
        report_or_exit_through(
            tel,
            &[Diagnostic::error(LOWER_UNBOUND, "no `main/0` fn found", Span::DUMMY)],
        );
        exit(1);
    };
    // fz-swt.10 — attach the IR Module so `fz_make_resource` (callable
    // from JIT'd code) can resolve dtor closures.
    let mut rt = Runtime::new(compiled.image.compiled_module(), 1, tel).with_module(&compiled.module);
    let _main_pid = rt.spawn(main_fn);
    notify_fixture_execution_start();
    rt.run_until_idle();
}

#[cfg(test)]
#[path = "lib_test.rs"]
mod lib_test;
