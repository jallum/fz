mod ast;
mod ast_value;
mod bitstr;
mod callsite_walk;
mod concrete_types;
mod diag;
mod eval;
mod frontend;
mod fz_ir;
mod ir_callgraph;
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
mod ir_branch_fold;
mod ir_brand_erase;
mod ir_const_bs;
mod ir_dce;
mod ir_fold;
mod ir_fuse;
mod ir_inline;
mod ir_lower;
mod ir_planner;
mod ir_reducer;
mod lexer;
mod macros;
mod matcher;
mod modules;
mod parking;
mod parser;
mod pattern_check;
mod pattern_matrix;
mod reducer;
mod repl;
mod resolve;
mod runtime;
mod spec_check;
mod spec_registry;
mod telemetry;
mod test_runner;
mod type_expr;
mod types;
mod value;
use crate::telemetry::Telemetry as _;
use crate::types::Types;
use modules::pipeline::{CompileMode, ProviderInputs};
use std::cell::RefCell;
use std::io::{IsTerminal, Read};
use std::rc::Rc;

const FZ_EXEC_READY_FD_ENV: &str = "FZ_EXEC_READY_FD";

pub(crate) fn notify_fixture_execution_start() {
    let Ok(raw_fd) = std::env::var(FZ_EXEC_READY_FD_ENV) else {
        return;
    };
    let Ok(fd) = raw_fd.parse::<libc::c_int>() else {
        return;
    };
    let byte = [1_u8];
    unsafe {
        let _ = libc::write(fd, byte.as_ptr().cast(), byte.len());
        let _ = libc::close(fd);
    }
}

fn main() {
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
                    std::process::exit(2);
                }
            }
            "--emit=stats" => {
                emit_stats = true;
            }
            a => args.push(a.to_string()),
        }
        i += 1;
    }

    let tel = telemetry::ConfiguredTelemetry::new();
    if let Some(ref path) = log_telemetry {
        match telemetry::JsonlBackend::new_file(std::path::Path::new(path)) {
            Ok(backend) => {
                tel.attach(&[], Box::new(backend));
            }
            Err(e) => {
                eprintln!("--log-telemetry {}: {}", path, e);
                std::process::exit(2);
            }
        }
    }
    let stats_handler = if emit_stats {
        let s = telemetry::StatsHandler::new();
        tel.attach(&[], s.handler());
        Some(s)
    } else {
        None
    };

    match args.first().map(String::as_str) {
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
                    std::process::exit(2);
                });
                if let Err(e) = repl::run_script(std::path::Path::new(&path)) {
                    eprintln!("repl: {}", e);
                    std::process::exit(1);
                }
            } else if let Err(e) = repl::run() {
                eprintln!("repl: {}", e);
                std::process::exit(1);
            }
        }
        Some("test") => {
            let src = args.get(1).cloned().unwrap_or_else(|| {
                eprintln!("fz test <path>");
                std::process::exit(2);
            });
            if let Err(e) = test_runner::run(std::path::Path::new(&src)) {
                eprintln!("{}", e);
                std::process::exit(1);
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
            if std::io::stdin().is_terminal() {
                if let Err(e) = repl::run() {
                    eprintln!("repl: {}", e);
                    std::process::exit(1);
                }
            } else {
                let mut src = String::new();
                if let Err(e) = std::io::stdin().read_to_string(&mut src) {
                    eprintln!("reading stdin: {}", e);
                    std::process::exit(1);
                }
                let providers = ProviderInputs::new(
                    modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string(),
                    Vec::new(),
                );
                run_jit_src(&tel, src, "<stdin>".into(), CompileMode::Normal, &providers);
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

impl telemetry::Handler for ConsoleBuildHandler {
    fn handle(&self, ev: &telemetry::Event<'_, '_, '_>) {
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
            n if n == ["fz", "build", "fzi_failed"] => {
                eprintln!("fz build: failed to write .fzi artifacts: {}", s("error"));
            }
            // linking / linked are silent at default verbosity — the
            // build subcommand has historically been silent on success.
            _ => {}
        }
    }
}

fn run_build(tel: &telemetry::ConfiguredTelemetry, args: &[String]) {
    let sm_cell: Rc<RefCell<diag::SourceMap>> = Rc::new(RefCell::new(diag::SourceMap::new()));
    tel.attach(
        &["fz", "diag"],
        Box::new(telemetry::DiagRenderer::new_stderr(sm_cell.clone())),
    );
    tel.attach(&["fz", "build"], Box::new(ConsoleBuildHandler));

    let mut t = types::ConcreteTypes;
    let mut src_path: Option<String> = None;
    let mut out_path: Option<String> = None;
    let mut artifact_root = modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string();
    let mut emit_fzi = false;
    let mut emit_fzo = false;
    let mut mode = CompileMode::Normal;
    let mut provider_modules = Vec::new();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--lto" | "--whole-program" => mode = CompileMode::Lto,
            "--emit-fzi" => emit_fzi = true,
            "--emit-fzo" => emit_fzo = true,
            "--artifact-root" => {
                i += 1;
                artifact_root = args.get(i).cloned().unwrap_or_else(|| {
                    eprintln!("fz build: --artifact-root expects a path");
                    std::process::exit(2);
                });
            }
            "--interface" | "--provider" => {
                i += 1;
                let module = args.get(i).cloned().unwrap_or_else(|| {
                    eprintln!("fz build: --interface expects a module name");
                    std::process::exit(2);
                });
                provider_modules.push(parse_module_name_arg("fz build", &module));
            }
            "-o" => {
                i += 1;
                out_path = args.get(i).cloned();
                if out_path.is_none() {
                    eprintln!("fz build: -o expects a path");
                    std::process::exit(2);
                }
            }
            a if !a.starts_with('-') && src_path.is_none() => {
                src_path = Some(a.to_string());
            }
            a => {
                eprintln!("fz build: unknown arg `{}`", a);
                std::process::exit(2);
            }
        }
        i += 1;
    }
    let src_path = src_path.unwrap_or_else(|| {
        eprintln!(
            "fz build [--lto] [--emit-fzi] [--emit-fzo] [--interface <Module>] [--artifact-root <dir>] <src.fz> -o <out>"
        );
        std::process::exit(2);
    });
    let out_path = out_path.unwrap_or_else(|| {
        eprintln!("fz build: -o <out> is required");
        std::process::exit(2);
    });
    let src = std::fs::read_to_string(&src_path).unwrap_or_else(|e| {
        eprintln!("read {}: {}", src_path, e);
        std::process::exit(1);
    });

    let fzo_source = emit_fzo.then(|| src.clone());
    let providers = ProviderInputs::new(artifact_root.clone(), provider_modules);
    let frontend_result = modules::pipeline::compile_source_with_providers(
        &mut t,
        src,
        src_path.clone(),
        &providers,
        tel,
    )
    .unwrap_or_else(|err| report_pipeline_error_or_exit("fz build", tel, &sm_cell, err));
    let prepared = checked_module_or_exit("fz build", &mut t, frontend_result, &sm_cell, tel, mode);
    if emit_fzi || emit_fzo {
        let diags = modules::interface::validate_public_export_specs(&prepared.interfaces);
        diag::report_or_exit_through(tel, &diags);
    }
    if emit_fzi {
        let store = modules::artifact_store::ArtifactStore::new(&artifact_root);
        store
            .write_fzi_artifacts_with_telemetry(tel, &prepared.interfaces)
            .unwrap_or_else(|e| {
                tel.event(
                    &["fz", "build", "fzi_failed"],
                    metadata! { error: e.to_string() },
                );
                std::process::exit(1);
            });
    }

    let graph = modules::pipeline::prepare_execution_graph(&mut t, prepared, &providers, tel, mode)
        .unwrap_or_else(|err| report_pipeline_error_or_exit("fz build", tel, &sm_cell, err));

    if emit_fzo {
        let unit = graph
            .units
            .first()
            .expect("execution graph includes root unit");
        let fzo = modules::artifact::FzoArtifact::from_unit_source(
            unit,
            fzo_source.expect("emit_fzo source"),
            vec![
                "kind=source-compiled-module".to_string(),
                format!("source={src_path}"),
            ],
        );
        let store = modules::artifact_store::ArtifactStore::new(&artifact_root);
        store
            .write_fzo_artifacts_with_telemetry(tel, [&fzo])
            .unwrap_or_else(|e| {
                tel.event(
                    &["fz", "build", "fzo_failed"],
                    metadata! { error: e.to_string() },
                );
                std::process::exit(1);
            });
    }

    let obj_name = std::path::Path::new(&src_path)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("fz_program");
    let artifact =
        ir_codegen::compile_aot_pretyped(&mut t, &graph.module, &graph.module_plan, obj_name, tel)
            .unwrap_or_else(|e| {
                diag::report_or_exit_through(tel, &[e.to_diagnostic()]);
                std::process::exit(1);
            });

    if artifact.main_symbol.is_none() {
        tel.emit(&["fz", "build", "no_main"]);
        std::process::exit(1);
    }
    // fz-d5b — gate on errors. `collect_diagnostics` emits Severity::Error
    // for soundness leaks (TYPE_OPAQUE_VISIBILITY, TYPE_OPAQUE_ARITHMETIC,
    // TYPE_IMPURE_RECEIVE_GUARD); before this gate they rendered but the
    // build continued, masking the rejection.
    diag::report_or_exit_through(tel, artifact.diagnostics.as_slice());

    // Write the object next to the output, then invoke cc.
    let obj_temp = std::path::PathBuf::from(format!("{}.o", out_path));
    std::fs::write(&obj_temp, &artifact.object).unwrap_or_else(|e| {
        tel.event(
            &["fz", "build", "write_obj_failed"],
            metadata! { path: obj_temp.display().to_string(), error: e.to_string() },
        );
        std::process::exit(1);
    });

    // Locate libfz_runtime.a. Prefer the deps/ artifact — it is rebuilt
    // in lockstep with the rlib on every `cargo build` and is always
    // fresh. The top-level target/<profile>/libfz_runtime.a is only
    // updated when the runtime crate is built as the primary target, so
    // it can lag behind when fz is the primary crate (fz-ul4.33).
    let exe = std::env::current_exe().unwrap_or_else(|_| std::path::PathBuf::from("fz"));
    let target_dir = exe
        .parent()
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| std::path::PathBuf::from("target/debug"));
    let deps_dir = target_dir.join("deps");
    let runtime_a = std::fs::read_dir(&deps_dir)
        .ok()
        .and_then(|rd| {
            rd.filter_map(|e| e.ok())
                .filter(|e| {
                    let n = e.file_name();
                    let s = n.to_string_lossy();
                    s.starts_with("libfz_runtime-") && s.ends_with(".a")
                })
                .max_by_key(|e| e.metadata().and_then(|m| m.modified()).ok())
                .map(|e| e.path())
        })
        .unwrap_or_else(|| target_dir.join("libfz_runtime.a"));

    let mut cc = std::process::Command::new("cc");
    cc.arg("-o").arg(&out_path).arg(&obj_temp).arg(&runtime_a);
    if cfg!(target_os = "macos") {
        cc.arg("-Wl,-undefined,dynamic_lookup");
    }
    tel.event(
        &["fz", "build", "linking"],
        metadata! { output: out_path.clone() },
    );
    let status = cc.status().unwrap_or_else(|e| {
        tel.event(
            &["fz", "build", "cc_failed"],
            metadata! { error: e.to_string() },
        );
        std::process::exit(1);
    });
    if !status.success() {
        tel.event(
            &["fz", "build", "cc_exit"],
            metadata! { status: status.to_string() },
        );
        std::process::exit(1);
    }
    tel.event(
        &["fz", "build", "linked"],
        metadata! { output: out_path.clone() },
    );
    // Drop the intermediate .o on success.
    let _ = std::fs::remove_file(&obj_temp);
}

/// `fz interp <src.fz>` — run a program through the rebuilt IR interpreter
/// (ir_interp). The interp walks fz_ir::Module directly using the same
/// tagged-ref rep, heap, and runtime FFI as the JIT.
///
/// Coverage grows feature-by-feature across fz-ul4.23.5.2 → .5.8. If the
/// interp hits an IR construct it doesn't yet support, it returns a
/// "not yet supported" error and exits 75 (EX_TEMPFAIL) so the fixture
/// matrix logs the path as Deferred rather than failing.
fn run_interp(tel: &telemetry::ConfiguredTelemetry, args: &[String]) {
    let sm_cell: Rc<RefCell<diag::SourceMap>> = Rc::new(RefCell::new(diag::SourceMap::new()));
    tel.attach(
        &["fz", "diag"],
        Box::new(telemetry::DiagRenderer::new_stderr(sm_cell.clone())),
    );

    let mut t = types::ConcreteTypes;
    let path = args.first().cloned().unwrap_or_else(|| {
        eprintln!("fz interp <src.fz>");
        std::process::exit(2);
    });
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("read {}: {}", path, e);
        std::process::exit(1);
    });
    let providers = ProviderInputs::new(
        modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string(),
        Vec::new(),
    );
    let frontend_result =
        modules::pipeline::compile_source_with_providers(&mut t, src, path, &providers, tel)
            .unwrap_or_else(|err| report_pipeline_error_or_exit("fz interp", tel, &sm_cell, err));
    let checked = checked_module_or_exit(
        "fz interp",
        &mut t,
        frontend_result,
        &sm_cell,
        tel,
        CompileMode::Normal,
    );
    let graph = modules::pipeline::prepare_execution_graph(
        &mut t,
        checked,
        &providers,
        tel,
        CompileMode::Normal,
    )
    .unwrap_or_else(|err| report_pipeline_error_or_exit("fz interp", tel, &sm_cell, err));
    notify_fixture_execution_start();
    match ir_interp::run_main(tel, &graph.module) {
        Ok(_halt) => {}
        Err(msg) => {
            eprintln!("fz interp: {}", msg);
            // Treat "not yet supported" errors as graceful Deferred so the
            // matrix can roll out interp coverage incrementally.
            if msg.contains("not yet supported") {
                std::process::exit(75);
            }
            std::process::exit(1);
        }
    }
}

fn run_jit_from_path(tel: &telemetry::ConfiguredTelemetry, args: &[String]) {
    let mut mode = CompileMode::Normal;
    let mut src_path: Option<String> = None;
    let mut artifact_root = modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string();
    let mut provider_modules = Vec::new();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--lto" | "--whole-program" => mode = CompileMode::Lto,
            "--artifact-root" => {
                i += 1;
                artifact_root = args.get(i).cloned().unwrap_or_else(|| {
                    eprintln!("fz run: --artifact-root expects a path");
                    std::process::exit(2);
                });
            }
            "--interface" | "--provider" => {
                i += 1;
                let module = args.get(i).cloned().unwrap_or_else(|| {
                    eprintln!("fz run: --interface expects a module name");
                    std::process::exit(2);
                });
                provider_modules.push(parse_module_name_arg("fz run", &module));
            }
            a if !a.starts_with("--") && src_path.is_none() => src_path = Some(a.to_string()),
            a => {
                eprintln!("fz run: unknown arg `{}`", a);
                std::process::exit(2);
            }
        }
        i += 1;
    }
    let src_path = src_path.unwrap_or_else(|| {
        eprintln!("fz run [--lto] [--interface <Module>] [--artifact-root <dir>] <src.fz>");
        std::process::exit(2);
    });
    let src = std::fs::read_to_string(&src_path).unwrap_or_else(|e| {
        eprintln!("read {}: {}", src_path, e);
        std::process::exit(1);
    });
    let providers = ProviderInputs::new(artifact_root, provider_modules);
    run_jit_src(tel, src, src_path, mode, &providers);
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
fn format_clif(text: &str, sm: &diag::SourceMap) -> String {
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
                    let file_id = diag::FileId(bits >> 24);
                    let offset = bits & 0x00FF_FFFF;
                    if (file_id.0 as usize) < sm.file_count() {
                        let loc = sm.locate(diag::Span::new(file_id, offset, offset));
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
        let indent = if is_top || is_block_header {
            ""
        } else {
            "    "
        };

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

impl telemetry::Handler for ConsoleDumpHandler {
    fn handle(&self, ev: &telemetry::Event<'_, '_, '_>) {
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

fn run_dump(tel: &telemetry::ConfiguredTelemetry, args: &[String]) {
    let sm_cell: Rc<RefCell<diag::SourceMap>> = Rc::new(RefCell::new(diag::SourceMap::new()));
    tel.attach(
        &["fz", "diag"],
        Box::new(telemetry::DiagRenderer::new_stderr(sm_cell.clone())),
    );
    tel.attach(&["fz", "dump"], Box::new(ConsoleDumpHandler));

    let mut path: Option<String> = None;
    let mut fn_filter: Option<String> = None;
    let mut emit = "clif".to_string();
    let mut show_all = false;
    let mut strict_interfaces = false;
    let mut artifact_root = modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string();
    let mut interface_modules = Vec::new();
    let mut mode = CompileMode::Normal;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--emit" => {
                i += 1;
                emit = args.get(i).cloned().unwrap_or_else(|| {
                    eprintln!("fz dump: --emit expects a value (clif)");
                    std::process::exit(2);
                });
            }
            "--fn" => {
                i += 1;
                fn_filter = args.get(i).cloned();
                if fn_filter.is_none() {
                    eprintln!("fz dump: --fn expects a name");
                    std::process::exit(2);
                }
            }
            // fz-f88.7 — bypass dump_outcomes filtering (prelude + dead bodies).
            "--all" => show_all = true,
            "--strict-interfaces" => strict_interfaces = true,
            "--artifact-root" => {
                i += 1;
                artifact_root = args.get(i).cloned().unwrap_or_else(|| {
                    eprintln!("fz dump: --artifact-root expects a path");
                    std::process::exit(2);
                });
            }
            "--interface" => {
                i += 1;
                let module = args.get(i).cloned().unwrap_or_else(|| {
                    eprintln!("fz dump: --interface expects a module name");
                    std::process::exit(2);
                });
                interface_modules.push(parse_module_name_arg("fz dump", &module));
            }
            "--lto" | "--whole-program" => mode = CompileMode::Lto,
            a if !a.starts_with("--") && path.is_none() => path = Some(a.to_string()),
            a => {
                eprintln!("fz dump: unknown arg `{}`", a);
                std::process::exit(2);
            }
        }
        i += 1;
    }
    let path = path.unwrap_or_else(|| {
        eprintln!(
            "fz dump <src.fz> [--lto] [--interface <Module>] [--artifact-root <dir>] [--emit clif|asm|both|interfaces|specs|bodies|outcomes|stats] [--fn <name>]"
        );
        std::process::exit(2);
    });
    let emit_clif = matches!(emit.as_str(), "clif" | "both");
    let emit_asm = matches!(emit.as_str(), "asm" | "both");
    let emit_specs = emit.as_str() == "specs";
    let emit_interfaces = matches!(emit.as_str(), "interface" | "interfaces");
    let emit_stats = emit.as_str() == "stats";
    // fz-jg5.8 (RED.7) — user-facing diagnostic: list every emitted body
    // and (in v1) its source spec key. Boundary attribution per-call is a
    // follow-on; this v1 prints the spec set and a single-line summary so
    // the user can see "0 user fns" for fully-reduced programs.
    let emit_bodies = emit.as_str() == "bodies";
    // fz-9pr.16 — `outcomes`: per-callsite reducer/planner verdict diary.
    let emit_outcomes = emit.as_str() == "outcomes";
    if !emit_clif
        && !emit_asm
        && !emit_specs
        && !emit_interfaces
        && !emit_bodies
        && !emit_outcomes
        && !emit_stats
    {
        eprintln!(
            "fz dump: --emit must be one of `clif`, `asm`, `both`, `interfaces`, `specs`, `bodies`, `outcomes`, `stats`"
        );
        std::process::exit(2);
    }
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("read {}: {}", path, e);
        std::process::exit(1);
    });
    let interface_table =
        modules::pipeline::load_interface_table(&artifact_root, &interface_modules, tel)
            .unwrap_or_else(|err| report_pipeline_error_or_exit("fz dump", tel, &sm_cell, err));

    if emit_specs {
        if fn_filter.is_some() {
            eprintln!("fz dump: --fn is ignored with --emit specs (spec dump is per-module)");
        }
        let dump = dump_specs_pipeline(tel, &sm_cell, src, path.clone(), interface_table);
        tel.event(&["fz", "dump", "specs"], metadata! { text: dump });
        return;
    }

    if emit_interfaces {
        if fn_filter.is_some() {
            eprintln!("fz dump: --fn is ignored with --emit interfaces");
        }
        let dump = dump_interfaces_pipeline(
            tel,
            &sm_cell,
            src,
            path.clone(),
            strict_interfaces,
            interface_table,
        );
        tel.event(&["fz", "dump", "interfaces"], metadata! { text: dump });
        return;
    }

    if emit_bodies {
        if fn_filter.is_some() {
            eprintln!("fz dump: --fn is ignored with --emit bodies");
        }
        tel.event(
            &["fz", "dump", "bodies"],
            metadata! { text: dump_bodies_pipeline(tel, &sm_cell, src, path.clone(), mode) },
        );
        return;
    }

    if emit_outcomes {
        if fn_filter.is_some() {
            eprintln!("fz dump: --fn is ignored with --emit outcomes");
        }
        tel.event(
            &["fz", "dump", "outcomes"],
            metadata! { text: dump_outcomes_pipeline(tel, &sm_cell, src, path.clone(), show_all, mode) },
        );
        return;
    }

    if emit_stats {
        if fn_filter.is_some() {
            eprintln!("fz dump: --fn is ignored with --emit stats");
        }
        let providers = ProviderInputs::new(artifact_root.clone(), Vec::new());
        let _ = compile_pipeline(tel, &sm_cell, src, path.clone(), mode, &providers);
        return;
    }

    if emit_clif {
        ir_codegen::ir_text_record_enable();
    }
    if emit_asm {
        ir_codegen::asm_record_enable();
    }
    let providers = ProviderInputs::new(artifact_root.clone(), Vec::new());
    let compiled = compile_pipeline(tel, &sm_cell, src, path.clone(), mode, &providers);
    let clif_entries = if emit_clif {
        ir_codegen::ir_text_record_take()
    } else {
        Vec::new()
    };
    let asm_entries = if emit_asm {
        ir_codegen::asm_record_take()
    } else {
        Vec::new()
    };

    // Combine into a single fn-name → (clif?, asm?) map preserving order.
    let mut order: Vec<String> = Vec::new();
    let mut clif_map: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    let mut asm_map: std::collections::HashMap<String, String> = std::collections::HashMap::new();
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
            let suffix_match =
                name.starts_with(filter.as_str()) && name[filter.len()..].starts_with("_s");
            if name != filter && !suffix_match {
                continue;
            }
        }
        tel.event(
            &["fz", "dump", "fn_header"],
            metadata! { name: name.clone() },
        );
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
        std::process::exit(1);
    }
}

/// Run the frontend pipeline, updating `sm_cell` and routing diagnostics
/// through the bus. Exits(1) on error or on any `Severity::Error` diagnostic.
fn run_frontend(
    result: frontend::FrontendResult,
    sm_cell: &Rc<RefCell<diag::SourceMap>>,
    tel: &dyn telemetry::Telemetry,
) -> frontend::FrontendOk {
    let ok = result.unwrap_or_else(|err| {
        *sm_cell.borrow_mut() = err.sm;
        diag::report_or_exit_through(tel, err.diagnostics.as_slice());
        std::process::exit(1);
    });
    *sm_cell.borrow_mut() = ok.sm.clone();
    diag::report_or_exit_through(tel, ok.diagnostics.as_slice());
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
    image: ir_codegen::CompiledImage,
    main_fn: Option<fz_ir::FnId>,
    /// SourceMap surfaced so `fz dump` can resolve Cranelift's `@<hex>`
    /// srclocs back to `file:line:col`. fz-ul4.23.7.
    sm: diag::SourceMap,
    /// fz-swt.10 — IR Module kept alive past codegen so the runtime's
    /// `MakeResourceHook` thunk can walk dtor closure bodies.
    module: fz_ir::Module,
}

fn parse_module_name_arg(context: &str, text: &str) -> modules::identity::ModuleName {
    modules::identity::ModuleName::parse_dotted(text).unwrap_or_else(|err| {
        eprintln!("{context}: {err}");
        std::process::exit(2);
    })
}

fn report_pipeline_error_or_exit(
    context: &str,
    tel: &dyn telemetry::Telemetry,
    sm_cell: &Rc<RefCell<diag::SourceMap>>,
    err: modules::pipeline::PipelineError,
) -> ! {
    match err {
        modules::pipeline::PipelineError::Frontend(err) => {
            *sm_cell.borrow_mut() = err.sm;
            diag::report_or_exit_through(tel, err.diagnostics.as_slice());
        }
        modules::pipeline::PipelineError::Diagnostics { sm, diagnostics } => {
            if let Some(sm) = sm {
                *sm_cell.borrow_mut() = sm;
            }
            diag::report_or_exit_through(tel, diagnostics.as_slice());
        }
        modules::pipeline::PipelineError::DiagnosticVec { sm, diagnostics } => {
            if let Some(sm) = sm {
                *sm_cell.borrow_mut() = sm;
            }
            diag::report_or_exit_through(tel, &diagnostics);
        }
        modules::pipeline::PipelineError::Diagnostic(diagnostic) => {
            diag::report_or_exit_through(tel, &[diagnostic]);
        }
        modules::pipeline::PipelineError::Artifact(err) => {
            eprintln!("{context}: {err}");
        }
        modules::pipeline::PipelineError::Link(err) => {
            let diagnostic = modules::pipeline::link_error_diagnostic(err);
            diag::report_or_exit_through(tel, &[diagnostic]);
        }
        modules::pipeline::PipelineError::MissingFzoModule => {
            eprintln!("{context}: fzo artifact has no module identity");
        }
    }
    std::process::exit(1);
}

fn checked_module_or_exit(
    context: &str,
    t: &mut types::ConcreteTypes,
    result: frontend::FrontendResult,
    sm_cell: &Rc<RefCell<diag::SourceMap>>,
    tel: &dyn telemetry::Telemetry,
    mode: CompileMode,
) -> modules::pipeline::CheckedModule {
    let checked = modules::pipeline::checked_module_for_mode(t, result, tel, mode)
        .unwrap_or_else(|err| report_pipeline_error_or_exit(context, tel, sm_cell, err));
    *sm_cell.borrow_mut() = checked.sm.clone();
    diag::report_or_exit_through(tel, checked.diagnostics.as_slice());
    checked
}

/// fz-73m — drive a source string through lex → parse → resolve → macros
/// → ir_lower → plan_module, then pretty-print `ModulePlan` for golden
/// inspection. Skips codegen entirely; the dump is a planner-only view.
fn dump_specs_pipeline(
    tel: &dyn telemetry::Telemetry,
    sm_cell: &Rc<RefCell<diag::SourceMap>>,
    src: String,
    source_name: String,
    interface_table: resolve::InterfaceTable,
) -> String {
    let mut t = types::ConcreteTypes;
    let frontend = run_frontend(
        frontend::compile_source_with_interface_table(
            &mut t,
            src,
            source_name,
            interface_table,
            tel,
        ),
        sm_cell,
        tel,
    );
    ir_planner::pretty_module_plan(&mut t, &frontend.module, &frontend.module_plan)
}

fn dump_interfaces_pipeline(
    tel: &dyn telemetry::Telemetry,
    sm_cell: &Rc<RefCell<diag::SourceMap>>,
    src: String,
    source_name: String,
    strict: bool,
    interface_table: resolve::InterfaceTable,
) -> String {
    let mut t = types::ConcreteTypes;
    let frontend = run_frontend(
        frontend::compile_source_with_interface_table(
            &mut t,
            src,
            source_name,
            interface_table,
            tel,
        ),
        sm_cell,
        tel,
    );
    if strict {
        let diags =
            modules::interface::validate_public_export_specs(&frontend._prog.module_interfaces);
        diag::report_or_exit_through(tel, &diags);
    }
    modules::interface::render_interfaces(&frontend._prog.module_interfaces)
}

fn render_key_slots(t: &mut types::ConcreteTypes, key: &[types::KeySlot]) -> String {
    types::display_key_slots(t, key)
}

fn render_spec_key(
    t: &mut types::ConcreteTypes,
    spec_key: &ir_planner::fn_types::SpecKey,
) -> String {
    format!(
        "{} demand={}",
        render_key_slots(t, &spec_key.input),
        ir_planner::fn_types::display_return_demand(t, &spec_key.demand)
    )
}

fn render_dispatch_target<F: Fn(fz_ir::FnId) -> String>(
    t: &mut types::ConcreteTypes,
    fn_name: &F,
    target: &ir_planner::fn_types::SpecKey,
) -> String {
    format!(
        "{}#{} {}",
        fn_name(target.fn_id),
        target.fn_id.0,
        render_spec_key(t, target)
    )
}

/// fz-jg5.8 (RED.7) — `fz dump --emit bodies`: print every user fn that
/// survives the reducer with the spec keys codegen emits for it. A
/// program that fully reduces shows `bodies emitted: 0 user functions
/// (no boundaries — program fully reduces)`.
///
/// Each entry is `<fn_name>: <N> spec(s) [<key_1>] [<key_2>] ...`. The
/// dump runs the full compile pipeline (including the reducer); the
/// surviving fns and their spec keys are read out of `ModulePlan`.
fn dump_bodies_pipeline(
    tel: &dyn telemetry::Telemetry,
    sm_cell: &Rc<RefCell<diag::SourceMap>>,
    src: String,
    source_name: String,
    mode: CompileMode,
) -> String {
    use crate::ir_planner::ModulePlan;
    let mut t = types::ConcreteTypes;
    let frontend_result = frontend::compile_source_with_types(&mut t, src, source_name, tel);
    let prepared = checked_module_or_exit("fz dump", &mut t, frontend_result, sm_cell, tel, mode);
    let mut module = prepared.module;
    // Run the reducer pass directly so the bodies dump reflects what
    // codegen would see, without going all the way to JIT.
    let _ = ir_reducer::reduce_module_with_telemetry(&mut t, &mut module, tel);
    let mt: ModulePlan = ir_planner::plan_module(&mut t, &module, tel);

    // Group surviving specs by user-fn name. Skip the conventional
    // synthetic helpers (k_*, fn_clause_*, lambda_*) — they're
    // continuations or pattern-clause bodies, not user fns.
    let mut by_name: std::collections::BTreeMap<String, Vec<&ir_planner::fn_types::SpecKey>> =
        std::collections::BTreeMap::new();
    for spec_key in mt.specs.keys() {
        let Some(&idx) = module.fn_idx.get(&spec_key.fn_id) else {
            continue;
        };
        let name = &module.fns[idx].name;
        if name.starts_with("k_")
            || name.starts_with("fn_clause_")
            || name.starts_with("lambda_")
            || name == "main"
        {
            continue;
        }
        by_name.entry(name.clone()).or_default().push(spec_key);
    }

    let mut out = String::new();
    if by_name.is_empty() {
        out.push_str("bodies emitted: 0 user functions\n");
        out.push_str("  (no boundaries — program fully reduces)\n");
        return out;
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
            out.push_str(&format!("    {}\n", render_spec_key(&mut t, key)));
        }
    }
    out
}

/// fz-9pr.16 — `fz dump --emit outcomes`: per-callsite verdict diary.
///
/// Runs the codegen front half (lex → parse → resolve → macros →
/// ir_lower → reduce_module → plan_module) and prints every dispatch
/// entry in `mt.specs[*].dispatches` plus the reducer's
/// Consumed / Stalled log entries, grouped by caller fn. Output shape:
///
/// ```text
/// outcomes for <source>
///
/// <caller_fn>:
///   blk<id> <slot> -> <verdict>[ (<reason or target>)]
///   ...
/// ```
///
/// Use this to answer "why didn't X fold?" without a debugger — every
/// `Stalled` carries a `StalledReason`, every `Emitted` shows the
/// resolved spec key.
///
/// fz-f88.7 — by default, two classes of caller are hidden so the
/// signal stays focused on user-program code:
///   - callers whose `FnIr.category == Prelude` (print noise
///     that's the same in every fixture);
///   - callers whose `FnId` no longer has any reachable spec after
///     reduction (the body is dead-coded).
///
/// Pass `show_all=true` (CLI `--all`) to bypass both filters.
fn dump_outcomes_pipeline(
    tel: &dyn telemetry::Telemetry,
    sm_cell: &Rc<RefCell<diag::SourceMap>>,
    src: String,
    source_name: String,
    show_all: bool,
    mode: CompileMode,
) -> String {
    use crate::fz_ir::{CallsiteId, EmitSlot, FnId};
    let mut t = types::ConcreteTypes;
    let frontend_result =
        frontend::compile_source_with_types(&mut t, src, source_name.clone(), tel);
    let prepared = checked_module_or_exit("fz dump", &mut t, frontend_result, sm_cell, tel, mode);
    let mut module = prepared.module;
    let reducer_log = ir_reducer::reduce_module_with_telemetry(&mut t, &mut module, tel);
    let mt = ir_planner::plan_module(&mut t, &module, tel);

    let fn_name = |fid: fz_ir::FnId| -> String {
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
            EmitSlot::MakeClosure => "MakeClosure",
        }
    };
    let render_span = |sp: crate::diag::Span| -> String {
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
        Folded(crate::types::Ty),
        Static(ir_planner::fn_types::SpecKey),
        Indirect(ir_planner::fn_types::SpecKey),
        Stalled(fz_ir::StalledReason),
    }

    fn render_outcome<F: Fn(fz_ir::FnId) -> String>(
        t: &mut types::ConcreteTypes,
        fn_name: &F,
        outcome: &Outcome,
    ) -> String {
        match outcome {
            Outcome::Folded(v) => format!("Folded({})", t.display(v)),
            Outcome::Static(target) => {
                format!("Static({})", render_dispatch_target(t, fn_name, target))
            }
            Outcome::Indirect(target) => {
                format!("Indirect({})", render_dispatch_target(t, fn_name, target))
            }
            Outcome::Stalled(reason) => format!("Stalled({})", reason),
        }
    }

    // Rows grouped by (caller_fid, caller_key) → list of (cid, Dispatch).
    type Section = (ir_planner::fn_types::SpecKey, Vec<(CallsiteId, Outcome)>);
    type SortKey = (u32, String);
    type RowsBySpec = std::collections::BTreeMap<SortKey, Section>;
    let mut rows_by_spec: RowsBySpec = std::collections::BTreeMap::new();

    // Pre-collect cids that any spec dispatched, so reducer Stalled rows
    // at those cids are suppressed (their reason already rode through as
    // a spec-side decision — no point double-reporting).
    let mut spec_cids: std::collections::HashSet<CallsiteId> = std::collections::HashSet::new();
    for ft in mt.specs.values() {
        for cid in ft.dispatches.keys() {
            spec_cids.insert(cid.clone());
        }
    }

    let push_row = |rows_by_spec: &mut RowsBySpec,
                    caller_fid: FnId,
                    caller_key: &ir_planner::fn_types::SpecKey,
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
        for (cid, target) in ft.dispatches.iter() {
            let dispatch = match cid.slot {
                EmitSlot::ClosureCall => Outcome::Indirect(target.clone()),
                _ => Outcome::Static(target.clone()),
            };
            let sort_key = render_spec_key(&mut t, caller_key);
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

    // Reducer Folded rows. The reducer doesn't track which caller spec a
    // fold attached to — folds happen on the IR before per-spec typing.
    // Attach Folded rows to the any-key spec of the cid.caller (the body
    // the reducer rewrote). This mirrors pre-fz-try.11 grouping by
    // caller fn.
    let any = t.any();
    let any_key_for = |fid: FnId| -> Option<ir_planner::fn_types::SpecKey> {
        mt.specs
            .keys()
            .find(|key| {
                key.fn_id == fid
                    && key.demand.is_value()
                    && key
                        .input
                        .iter()
                        .all(|key| key.is_none() || key == &Some(any.clone()))
            })
            .cloned()
    };
    for (cid, result) in &reducer_log.consumed {
        let Some(key) = any_key_for(cid.caller) else {
            continue;
        };
        let sort_key = render_spec_key(&mut t, &key);
        push_row(
            &mut rows_by_spec,
            cid.caller,
            &key,
            cid.clone(),
            Outcome::Folded(result.clone()),
            sort_key,
        );
    }
    // Reducer Stalled rows — only when no planner-spec dispatched the cid.
    for (cid, reason) in &reducer_log.stalled {
        if spec_cids.contains(cid) {
            continue;
        }
        let Some(key) = any_key_for(cid.caller) else {
            continue;
        };
        let sort_key = render_spec_key(&mut t, &key);
        push_row(
            &mut rows_by_spec,
            cid.caller,
            &key,
            cid.clone(),
            Outcome::Stalled(*reason),
            sort_key,
        );
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
                    render_outcome(&mut t, &fn_name, &a.1)
                        .cmp(&render_outcome(&mut t, &fn_name, &b.1))
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
    // whose body has no surviving spec post-reduction. `--all` bypasses.
    let reachable_fids: std::collections::HashSet<fz_ir::FnId> =
        mt.specs.keys().map(|key| key.fn_id).collect();
    let should_show = |f: &fz_ir::FnIr| -> bool {
        if show_all {
            return true;
        }
        if f.category == fz_ir::FnCategory::Prelude {
            return false;
        }
        reachable_fids.contains(&f.id)
    };
    let module_fn_order: std::collections::HashMap<fz_ir::FnId, usize> = module
        .fns
        .iter()
        .enumerate()
        .map(|(i, f)| (f.id, i))
        .collect();
    type SectionRef<'a> = (
        SortKey,
        &'a ir_planner::fn_types::SpecKey,
        &'a Vec<(CallsiteId, Outcome)>,
    );
    let mut sections: Vec<SectionRef<'_>> = rows_by_spec
        .iter()
        .map(|(k, (sk, rs))| (k.clone(), sk, rs))
        .collect();
    sections.sort_by_key(|(k, _, _)| {
        (
            module_fn_order
                .get(&FnId(k.0))
                .copied()
                .unwrap_or(usize::MAX),
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
            render_spec_key(&mut t, caller_key)
        ));
        for (cid, dispatch) in rows {
            out.push_str(&format!(
                "  @{} {} -> {}\n",
                render_span(cid.ident.span()),
                slot_str(cid.slot),
                render_outcome(&mut t, &fn_name, dispatch),
            ));
        }
    }
    out
}

fn compile_pipeline(
    tel: &dyn telemetry::Telemetry,
    sm_cell: &Rc<RefCell<diag::SourceMap>>,
    src: String,
    source_name: String,
    mode: CompileMode,
    providers: &ProviderInputs,
) -> Compiled {
    let mut t = types::ConcreteTypes;
    let frontend_result =
        modules::pipeline::compile_source_with_providers(&mut t, src, source_name, providers, tel)
            .unwrap_or_else(|err| report_pipeline_error_or_exit("fz run", tel, sm_cell, err));
    let prepared = checked_module_or_exit("fz run", &mut t, frontend_result, sm_cell, tel, mode);
    let graph = modules::pipeline::prepare_execution_graph(&mut t, prepared, providers, tel, mode)
        .unwrap_or_else(|err| report_pipeline_error_or_exit("fz run", tel, sm_cell, err));
    let main_fn = graph.module.fn_by_name("main").map(|f| f.id);
    let executable = ir_codegen::compile_pretyped(&mut t, &graph.module, &graph.module_plan, tel)
        .unwrap_or_else(|e| {
            diag::report_or_exit_through(tel, &[e.to_diagnostic()]);
            std::process::exit(1);
        });
    tel.event(
        &["fz", "module", "unit_compiled"],
        metadata! {
            fns: graph.module.fns.len() as i64,
            atoms: graph.module.atom_names.len() as i64,
        },
    );
    // fz-d5b — gate on errors from the planner-side diagnostics
    // (TYPE_OPAQUE_VISIBILITY, TYPE_OPAQUE_ARITHMETIC,
    // TYPE_IMPURE_RECEIVE_GUARD). Severity::Warning entries print and
    // we continue; Severity::Error halts.
    diag::report_or_exit_through(tel, executable.diagnostics().as_slice());
    let image = if graph.units.len() == 1 {
        ir_codegen::CompiledProgram::new(graph.units[0].clone(), executable)
            .link_image_with_telemetry(tel)
    } else {
        Ok(ir_codegen::CompiledImage::from_linked_with_telemetry(
            tel,
            graph.units.len(),
            executable,
        ))
    }
    .unwrap_or_else(|err| {
        report_pipeline_error_or_exit(
            "fz run",
            tel,
            sm_cell,
            modules::pipeline::PipelineError::Link(err),
        )
    });
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
        sm: graph.sm,
        module: graph.module,
    }
}

/// `fz run <path>` (and the no-argument stdin route) — compile, then drive
/// the program through the Runtime so concurrency-using fixtures work
/// end-to-end.
fn run_jit_src(
    tel: &telemetry::ConfiguredTelemetry,
    src: String,
    source_name: String,
    mode: CompileMode,
    providers: &ProviderInputs,
) {
    let sm_cell: Rc<RefCell<diag::SourceMap>> = Rc::new(RefCell::new(diag::SourceMap::new()));
    tel.attach(
        &["fz", "diag"],
        Box::new(telemetry::DiagRenderer::new_stderr(sm_cell.clone())),
    );
    let compiled = compile_pipeline(tel, &sm_cell, src, source_name, mode, providers);
    let Some(main_fn) = compiled.main_fn else {
        diag::report_or_exit_through(
            tel,
            &[diag::Diagnostic::error(
                diag::codes::LOWER_UNBOUND,
                "no `main/0` fn found",
                diag::Span::DUMMY,
            )],
        );
        std::process::exit(1);
    };
    // fz-swt.10 — attach the IR Module so `fz_make_resource` (callable
    // from JIT'd code) can resolve dtor closures.
    let mut rt =
        runtime::Runtime::new(compiled.image.compiled_module(), 1).with_module(&compiled.module);
    let _main_pid = rt.spawn(main_fn);
    notify_fixture_execution_start();
    rt.run_until_idle();
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let tel = telemetry::ConfiguredTelemetry::new();
        let capture = telemetry::Capture::new();
        tel.attach(&["fz"], capture.handler());
        let sm_cell = Rc::new(RefCell::new(diag::SourceMap::new()));

        let _compiled = compile_pipeline(
            &tel,
            &sm_cell,
            src.to_string(),
            "telemetry.fz".to_string(),
            CompileMode::Lto,
            &ProviderInputs::new(
                modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string(),
                Vec::new(),
            ),
        );

        assert!(capture.contains(&["fz", "module", "interfaces_collected"]));
        assert!(capture.contains(&["fz", "lto", "interfaces_validated"]));
        assert!(capture.contains(&["fz", "lto", "boundaries_erased"]));
    }
}
