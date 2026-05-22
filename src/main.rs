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
mod ir_codegen;
mod ir_codegen_cont_stub;
mod ir_codegen_invariants;
mod ir_codegen_receive;
mod ir_interp;
// ir_liveness removed (fz-ul4.11.31 subsumes .11.30): frame schemas are
// uniformly `[cont_ptr, ...entry_params]` with every Var slot FzValue;
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
mod ir_reducer;
mod ir_typer;
mod lexer;
mod macros;
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
use std::io::{IsTerminal, Read};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("build") => {
            run_build(&args[1..]);
            return;
        }
        Some("run") => {
            run_jit_from_path(&args[1..]);
            return;
        }
        Some("dump") => {
            run_dump(&args[1..]);
            return;
        }
        Some("interp") => {
            run_interp(&args[1..]);
            return;
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
                return;
            }
            if let Err(e) = repl::run() {
                eprintln!("repl: {}", e);
                std::process::exit(1);
            }
            return;
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
            return;
        }
        _ => {}
    }

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
        return;
    }

    let mut src = String::new();
    if let Err(e) = std::io::stdin().read_to_string(&mut src) {
        eprintln!("reading stdin: {}", e);
        std::process::exit(1);
    }
    run_jit_src(src, "<stdin>".into());
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
/// Telemetry schema for the `fz build` pipeline. Events cover the
/// observable boundaries of the build: missing main, object write/link
/// failures, successful link. CLI usage/help text (`-o expects a path`,
/// argument parsing errors) stays on `eprintln!` — that's UX, not
/// observability.
#[allow(dead_code)]
const BUILD_SPEC: telemetry::Spec = telemetry::Spec::new(
    "fz_build",
    "fz build subcommand pipeline events.",
    &[
        telemetry::EventDecl::new(
            &["fz", "build", "no_main"],
            telemetry::Level::Error,
            "Compilation produced no main/0 fn; nothing to link.",
            &[],
            &[],
        ),
        telemetry::EventDecl::new(
            &["fz", "build", "write_obj_failed"],
            telemetry::Level::Error,
            "Writing the intermediate object file failed.",
            &[],
            &[
                telemetry::KeySpec::new("path", telemetry::KeyType::Str, "object file path"),
                telemetry::KeySpec::new("error", telemetry::KeyType::Str, "io error message"),
            ],
        ),
        telemetry::EventDecl::new(
            &["fz", "build", "linking"],
            telemetry::Level::Debug,
            "About to invoke cc to link.",
            &[],
            &[telemetry::KeySpec::new(
                "output",
                telemetry::KeyType::Str,
                "output binary path",
            )],
        ),
        telemetry::EventDecl::new(
            &["fz", "build", "linked"],
            telemetry::Level::Debug,
            "cc completed successfully; final binary written.",
            &[],
            &[telemetry::KeySpec::new(
                "output",
                telemetry::KeyType::Str,
                "output binary path",
            )],
        ),
        telemetry::EventDecl::new(
            &["fz", "build", "cc_failed"],
            telemetry::Level::Error,
            "Failed to invoke cc.",
            &[],
            &[telemetry::KeySpec::new(
                "error",
                telemetry::KeyType::Str,
                "io error message",
            )],
        ),
        telemetry::EventDecl::new(
            &["fz", "build", "cc_exit"],
            telemetry::Level::Error,
            "cc invocation returned a non-zero status.",
            &[],
            &[telemetry::KeySpec::new(
                "status",
                telemetry::KeyType::Str,
                "exit-status display string",
            )],
        ),
    ],
);

struct ConsoleBuildHandler;

impl telemetry::Handler for ConsoleBuildHandler {
    fn handle(&self, ev: &telemetry::Event<'_>) {
        use telemetry::Value;
        let s = |k: &str| -> std::borrow::Cow<'static, str> {
            match ev.metadata.get(k) {
                Some(Value::Str(s)) => s.clone(),
                _ => std::borrow::Cow::Borrowed(""),
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
            // linking / linked are silent at default verbosity — the
            // build subcommand has historically been silent on success.
            _ => {}
        }
    }
}

fn run_build(args: &[String]) {
    let mut t = types::ConcreteTypes;
    let mut src_path: Option<String> = None;
    let mut out_path: Option<String> = None;
    let mut log_telemetry: Option<String> = None;
    let mut emit_stats = false;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "-o" => {
                i += 1;
                out_path = args.get(i).cloned();
                if out_path.is_none() {
                    eprintln!("fz build: -o expects a path");
                    std::process::exit(2);
                }
            }
            "--log-telemetry" => {
                i += 1;
                log_telemetry = args.get(i).cloned();
                if log_telemetry.is_none() {
                    eprintln!("fz build: --log-telemetry expects a path");
                    std::process::exit(2);
                }
            }
            "--emit=stats" => {
                emit_stats = true;
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
        eprintln!("fz build <src.fz> -o <out>");
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

    let frontend = frontend::compile_source_with_types(&mut t, src, src_path.clone())
        .unwrap_or_else(|err| {
            diag::report_or_exit(err.diagnostics.as_slice(), &err.sm);
            std::process::exit(1);
        });
    diag::report_or_exit(frontend.diagnostics.as_slice(), &frontend.sm);
    let obj_name = std::path::Path::new(&src_path)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("fz_program");
    let artifact =
        ir_codegen::compile_aot(&mut t, &frontend.module, obj_name).unwrap_or_else(|e| {
            diag::render_one_to_stderr(&frontend.sm, &e.to_diagnostic());
            std::process::exit(1);
        });
    let build_tel = telemetry::ConfiguredTelemetry::new();
    build_tel.attach(&["fz", "build"], Box::new(ConsoleBuildHandler));
    if let Some(ref path) = log_telemetry {
        match telemetry::JsonlBackend::new_file(std::path::Path::new(path)) {
            Ok(backend) => {
                build_tel.attach(&[], Box::new(backend));
            }
            Err(e) => {
                eprintln!("fz build: --log-telemetry {}: {}", path, e);
                std::process::exit(2);
            }
        }
    }
    let stats_handler = if emit_stats {
        let s = telemetry::StatsHandler::new();
        build_tel.attach(&[], s.handler());
        Some(s)
    } else {
        None
    };
    if artifact.main_symbol.is_none() {
        build_tel.execute(
            &["fz", "build", "no_main"],
            &telemetry::Measurements::new(),
            &telemetry::Metadata::new(),
        );
        std::process::exit(1);
    }
    // fz-d5b — gate on errors. `collect_diagnostics` emits Severity::Error
    // for soundness leaks (TYPE_OPAQUE_VISIBILITY, TYPE_OPAQUE_ARITHMETIC,
    // TYPE_IMPURE_RECEIVE_GUARD); before this gate they rendered but the
    // build continued, masking the rejection.
    diag::report_or_exit(artifact.diagnostics.as_slice(), &frontend.sm);

    // Write the object next to the output, then invoke cc.
    let obj_temp = std::path::PathBuf::from(format!("{}.o", out_path));
    std::fs::write(&obj_temp, &artifact.object).unwrap_or_else(|e| {
        build_tel.execute(
            &["fz", "build", "write_obj_failed"],
            &telemetry::Measurements::new(),
            &metadata! { path: obj_temp.display().to_string(), error: e.to_string() },
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
    build_tel.execute(
        &["fz", "build", "linking"],
        &telemetry::Measurements::new(),
        &metadata! { output: out_path.clone() },
    );
    let status = cc.status().unwrap_or_else(|e| {
        build_tel.execute(
            &["fz", "build", "cc_failed"],
            &telemetry::Measurements::new(),
            &metadata! { error: e.to_string() },
        );
        std::process::exit(1);
    });
    if !status.success() {
        build_tel.execute(
            &["fz", "build", "cc_exit"],
            &telemetry::Measurements::new(),
            &metadata! { status: status.to_string() },
        );
        std::process::exit(1);
    }
    build_tel.execute(
        &["fz", "build", "linked"],
        &telemetry::Measurements::new(),
        &metadata! { output: out_path.clone() },
    );
    // Drop the intermediate .o on success.
    let _ = std::fs::remove_file(&obj_temp);
    if let Some(s) = stats_handler {
        s.print_summary();
    }
}

/// `fz interp <src.fz>` — run a program through the rebuilt IR interpreter
/// (ir_interp). The interp walks fz_ir::Module directly using the same
/// FzValue rep, heap, and runtime FFI as the JIT.
///
/// Coverage grows feature-by-feature across fz-ul4.23.5.2 → .5.8. If the
/// interp hits an IR construct it doesn't yet support, it returns a
/// "not yet supported" error and exits 75 (EX_TEMPFAIL) so the fixture
/// matrix logs the path as Deferred rather than failing.
fn run_interp(args: &[String]) {
    let mut t = types::ConcreteTypes;
    let path = args.first().cloned().unwrap_or_else(|| {
        eprintln!("fz interp <src.fz>");
        std::process::exit(2);
    });
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("read {}: {}", path, e);
        std::process::exit(1);
    });
    let frontend = frontend::compile_source_with_types(&mut t, src, path).unwrap_or_else(|err| {
        diag::report_or_exit(err.diagnostics.as_slice(), &err.sm);
        std::process::exit(1);
    });
    diag::report_or_exit(frontend.diagnostics.as_slice(), &frontend.sm);
    match ir_interp::run_main(&frontend.module) {
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

fn run_jit_from_path(args: &[String]) {
    let src_path = args.first().cloned().unwrap_or_else(|| {
        eprintln!("fz run <src.fz>");
        std::process::exit(2);
    });
    let src = std::fs::read_to_string(&src_path).unwrap_or_else(|e| {
        eprintln!("read {}: {}", src_path, e);
        std::process::exit(1);
    });
    run_jit_src(src, src_path);
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

/// Telemetry schema for the `fz dump` subcommand. Every artifact a
/// dump produces (CLIF, asm, specs, bodies, outcomes) flows through a
/// matching event in this family; the default console handler prints
/// each artifact's text to stdout (or stderr for the no-match note).
#[allow(dead_code)]
const DUMP_SPEC: telemetry::Spec = telemetry::Spec::new(
    "fz_dump",
    "fz dump subcommand artifacts and per-fn rendering.",
    &[
        telemetry::EventDecl::new(
            &["fz", "dump", "fn_header"],
            telemetry::Level::Info,
            "`; fn <name>` separator preceding per-fn artifacts.",
            &[],
            &[telemetry::KeySpec::new(
                "name",
                telemetry::KeyType::Str,
                "fn name",
            )],
        ),
        telemetry::EventDecl::new(
            &["fz", "dump", "clif"],
            telemetry::Level::Info,
            "Rendered CLIF text for one fn.",
            &[],
            &[telemetry::KeySpec::new(
                "text",
                telemetry::KeyType::Str,
                "CLIF body",
            )],
        ),
        telemetry::EventDecl::new(
            &["fz", "dump", "asm"],
            telemetry::Level::Info,
            "Rendered asm text for one fn.",
            &[],
            &[telemetry::KeySpec::new(
                "text",
                telemetry::KeyType::Str,
                "asm body",
            )],
        ),
        telemetry::EventDecl::new(
            &["fz", "dump", "asm_separator"],
            telemetry::Level::Info,
            "`; ---- asm ----` line between CLIF and asm in `--emit both`.",
            &[],
            &[],
        ),
        telemetry::EventDecl::new(
            &["fz", "dump", "specs"],
            telemetry::Level::Info,
            "Full specs-block text (`--emit specs`).",
            &[],
            &[telemetry::KeySpec::new(
                "text",
                telemetry::KeyType::Str,
                "specs dump",
            )],
        ),
        telemetry::EventDecl::new(
            &["fz", "dump", "bodies"],
            telemetry::Level::Info,
            "Full bodies-block text (`--emit bodies`).",
            &[],
            &[telemetry::KeySpec::new(
                "text",
                telemetry::KeyType::Str,
                "bodies dump",
            )],
        ),
        telemetry::EventDecl::new(
            &["fz", "dump", "outcomes"],
            telemetry::Level::Info,
            "Full outcomes-block text (`--emit outcomes`).",
            &[],
            &[telemetry::KeySpec::new(
                "text",
                telemetry::KeyType::Str,
                "outcomes dump",
            )],
        ),
        telemetry::EventDecl::new(
            &["fz", "dump", "no_fn_match"],
            telemetry::Level::Warn,
            "User --fn filter matched no rendered fn.",
            &[],
            &[
                telemetry::KeySpec::new("filter", telemetry::KeyType::Str, "filter argument"),
                telemetry::KeySpec::new(
                    "available",
                    telemetry::KeyType::Str,
                    "comma-separated list of available names",
                ),
            ],
        ),
    ],
);

struct ConsoleDumpHandler;

impl telemetry::Handler for ConsoleDumpHandler {
    fn handle(&self, ev: &telemetry::Event<'_>) {
        use telemetry::Value;
        let text = |key: &str| -> Option<std::borrow::Cow<'static, str>> {
            match ev.metadata.get(key) {
                Some(Value::Str(s)) => Some(s.clone()),
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

fn run_dump(args: &[String]) {
    let mut path: Option<String> = None;
    let mut fn_filter: Option<String> = None;
    let mut emit = "clif".to_string();
    let mut show_all = false;
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
            a if !a.starts_with("--") && path.is_none() => path = Some(a.to_string()),
            a => {
                eprintln!("fz dump: unknown arg `{}`", a);
                std::process::exit(2);
            }
        }
        i += 1;
    }
    let path = path.unwrap_or_else(|| {
        eprintln!("fz dump <src.fz> [--emit clif|asm|both|specs|bodies|outcomes] [--fn <name>]");
        std::process::exit(2);
    });
    let emit_clif = matches!(emit.as_str(), "clif" | "both");
    let emit_asm = matches!(emit.as_str(), "asm" | "both");
    let emit_specs = emit.as_str() == "specs";
    // fz-jg5.8 (RED.7) — user-facing diagnostic: list every emitted body
    // and (in v1) its source spec key. Boundary attribution per-call is a
    // follow-on; this v1 prints the spec set and a single-line summary so
    // the user can see "0 user fns" for fully-reduced programs.
    let emit_bodies = emit.as_str() == "bodies";
    // fz-9pr.16 — `outcomes`: per-callsite reducer/typer verdict diary.
    let emit_outcomes = emit.as_str() == "outcomes";
    if !emit_clif && !emit_asm && !emit_specs && !emit_bodies && !emit_outcomes {
        eprintln!(
            "fz dump: --emit must be one of `clif`, `asm`, `both`, `specs`, `bodies`, `outcomes`"
        );
        std::process::exit(2);
    }
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("read {}: {}", path, e);
        std::process::exit(1);
    });

    let dump_tel = telemetry::ConfiguredTelemetry::new();
    dump_tel.attach(&["fz", "dump"], Box::new(ConsoleDumpHandler));

    if emit_specs {
        if fn_filter.is_some() {
            eprintln!("fz dump: --fn is ignored with --emit specs (spec dump is per-module)");
        }
        let dump = dump_specs_pipeline(src, path.clone());
        dump_tel.execute(
            &["fz", "dump", "specs"],
            &telemetry::Measurements::new(),
            &metadata! { text: dump },
        );
        return;
    }

    if emit_bodies {
        if fn_filter.is_some() {
            eprintln!("fz dump: --fn is ignored with --emit bodies");
        }
        dump_tel.execute(
            &["fz", "dump", "bodies"],
            &telemetry::Measurements::new(),
            &metadata! { text: dump_bodies_pipeline(src, path.clone()) },
        );
        return;
    }

    if emit_outcomes {
        if fn_filter.is_some() {
            eprintln!("fz dump: --fn is ignored with --emit outcomes");
        }
        dump_tel.execute(
            &["fz", "dump", "outcomes"],
            &telemetry::Measurements::new(),
            &metadata! { text: dump_outcomes_pipeline(src, path.clone(), show_all) },
        );
        return;
    }

    if emit_clif {
        ir_codegen::ir_text_record_enable();
    }
    if emit_asm {
        ir_codegen::asm_record_enable();
    }
    let compiled = compile_pipeline(src, path.clone());
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
        dump_tel.execute(
            &["fz", "dump", "fn_header"],
            &telemetry::Measurements::new(),
            &metadata! { name: name.clone() },
        );
        if emit_clif && let Some(text) = clif_map.get(name) {
            dump_tel.execute(
                &["fz", "dump", "clif"],
                &telemetry::Measurements::new(),
                &metadata! { text: format_clif(text, &compiled.sm) },
            );
        }
        if emit_asm && let Some(text) = asm_map.get(name) {
            if emit_clif {
                dump_tel.execute(
                    &["fz", "dump", "asm_separator"],
                    &telemetry::Measurements::new(),
                    &telemetry::Metadata::new(),
                );
            }
            dump_tel.execute(
                &["fz", "dump", "asm"],
                &telemetry::Measurements::new(),
                &metadata! { text: text.clone() },
            );
        }
        printed += 1;
    }
    if let Some(filter) = &fn_filter
        && printed == 0
    {
        dump_tel.execute(
            &["fz", "dump", "no_fn_match"],
            &telemetry::Measurements::new(),
            &metadata! { filter: filter.clone(), available: order.join(", ") },
        );
        std::process::exit(1);
    }
}

/// Drive a source string through the lex → parse → resolve → macros →
/// ir_lower → ir_codegen stages. Returns the compiled module; callers
/// either execute (`fz run`) or inspect (`fz dump`).
///
/// Single render path: every error from every stage goes through
/// diag::render_to_stderr. Lex / parse errors carry proper spans; later-
/// stage errors carry the spans threaded in by fz-ul4.20 / .21.
struct Compiled {
    cm: ir_codegen::CompiledModule,
    main_fn: Option<fz_ir::FnId>,
    /// SourceMap surfaced so `fz dump` can resolve Cranelift's `@<hex>`
    /// srclocs back to `file:line:col`. fz-ul4.23.7.
    sm: diag::SourceMap,
    /// fz-swt.10 — IR Module kept alive past codegen so the runtime's
    /// `MakeResourceHook` thunk can walk dtor closure bodies.
    module: fz_ir::Module,
}

/// fz-73m — drive a source string through lex → parse → resolve → macros
/// → ir_lower → type_module, then pretty-print `ModuleTypes` for golden
/// inspection. Skips codegen entirely; the dump is a typer-only view.
fn dump_specs_pipeline(src: String, source_name: String) -> String {
    let mut t = types::ConcreteTypes;
    let frontend =
        frontend::compile_source_with_types(&mut t, src, source_name).unwrap_or_else(|err| {
            diag::report_or_exit(err.diagnostics.as_slice(), &err.sm);
            std::process::exit(1);
        });
    diag::report_or_exit(frontend.diagnostics.as_slice(), &frontend.sm);
    let mt = ir_typer::type_module(&mut t, &frontend.module);
    ir_typer::pretty_module_types(&mut t, &frontend.module, &mt)
}

fn render_ty_key(t: &mut types::ConcreteTypes, key: &[types::Ty]) -> String {
    let parts: Vec<String> = key.iter().map(|key_ty| t.display(key_ty)).collect();
    format!("[{}]", parts.join(", "))
}

fn render_dispatch_target<F: Fn(fz_ir::FnId) -> String>(
    t: &mut types::ConcreteTypes,
    fn_name: &F,
    fid: fz_ir::FnId,
    key: &[types::Ty],
) -> String {
    format!("{}#{} {}", fn_name(fid), fid.0, render_ty_key(t, key))
}

fn render_dispatch<F: Fn(fz_ir::FnId) -> String>(
    t: &mut types::ConcreteTypes,
    fn_name: &F,
    dispatch: &fz_ir::Dispatch,
) -> String {
    match dispatch {
        fz_ir::Dispatch::Folded(v) => format!("Folded({})", t.display(v)),
        fz_ir::Dispatch::Static(fid, key) => {
            format!("Static({})", render_dispatch_target(t, fn_name, *fid, key))
        }
        fz_ir::Dispatch::Indirect(fid, key) => {
            format!(
                "Indirect({})",
                render_dispatch_target(t, fn_name, *fid, key)
            )
        }
        fz_ir::Dispatch::Stalled(reason) => format!("Stalled({})", reason),
    }
}

/// fz-jg5.8 (RED.7) — `fz dump --emit bodies`: print every user fn that
/// survives the reducer with the spec keys codegen emits for it. A
/// program that fully reduces shows `bodies emitted: 0 user functions
/// (no boundaries — program fully reduces)`.
///
/// Each entry is `<fn_name>: <N> spec(s) [<key_1>] [<key_2>] ...`. The
/// dump runs the full compile pipeline (including the reducer); the
/// surviving fns and their spec keys are read out of `ModuleTypes`.
fn dump_bodies_pipeline(src: String, source_name: String) -> String {
    use crate::ir_typer::ModuleTypes;
    let mut t = types::ConcreteTypes;
    let frontend =
        frontend::compile_source_with_types(&mut t, src, source_name).unwrap_or_else(|err| {
            diag::report_or_exit(err.diagnostics.as_slice(), &err.sm);
            std::process::exit(1);
        });
    diag::report_or_exit(frontend.diagnostics.as_slice(), &frontend.sm);
    let mut module = frontend.module;
    // Run the reducer pass directly so the bodies dump reflects what
    // codegen would see, without going all the way to JIT.
    let _ = ir_reducer::reduce_module(&mut t, &mut module);
    let mt: ModuleTypes = ir_typer::type_module(&mut t, &module);

    // Group surviving specs by user-fn name. Skip the conventional
    // synthetic helpers (k_*, fn_clause_*, lambda_*) — they're
    // continuations or pattern-clause bodies, not user fns.
    let mut by_name: std::collections::BTreeMap<String, Vec<&Vec<crate::types::Ty>>> =
        std::collections::BTreeMap::new();
    for (fid, key) in mt.specs.keys() {
        let Some(&idx) = module.fn_idx.get(fid) else {
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
        by_name.entry(name.clone()).or_default().push(key);
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
            out.push_str(&format!("    {}\n", render_ty_key(&mut t, key)));
        }
    }
    out
}

/// fz-9pr.16 — `fz dump --emit outcomes`: per-callsite verdict diary.
///
/// Runs the codegen front half (lex → parse → resolve → macros →
/// ir_lower → reduce_module → type_module) and prints every dispatch
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
///   - callers whose `FnIr.category == Prelude` (vec_get/print noise
///     that's the same in every fixture);
///   - callers whose `FnId` no longer has any reachable spec after
///     reduction (the body is dead-coded).
///
/// Pass `show_all=true` (CLI `--all`) to bypass both filters.
fn dump_outcomes_pipeline(src: String, source_name: String, show_all: bool) -> String {
    use crate::fz_ir::{CallsiteId, EmitSlot, FnId};
    let mut t = types::ConcreteTypes;
    let frontend = frontend::compile_source_with_types(&mut t, src, source_name.clone())
        .unwrap_or_else(|err| {
            diag::report_or_exit(err.diagnostics.as_slice(), &err.sm);
            std::process::exit(1);
        });
    diag::report_or_exit(frontend.diagnostics.as_slice(), &frontend.sm);
    let mut module = frontend.module;
    let reducer_log = ir_reducer::reduce_module(&mut t, &mut module);
    let mt = ir_typer::type_module(&mut t, &module);

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
    // The Dispatch enum separates the structural slot (where) from the
    // dispatch outcome (what).
    use fz_ir::Dispatch;

    // Rows grouped by (caller_fid, caller_key) → list of (cid, Dispatch).
    type SpecKey = (FnId, Vec<crate::types::Ty>);
    type Section = (SpecKey, Vec<(CallsiteId, Dispatch)>);
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
                    caller_key: &[crate::types::Ty],
                    cid: CallsiteId,
                    dispatch: Dispatch,
                    sort_key: String| {
        let entry = rows_by_spec
            .entry((caller_fid.0, sort_key))
            .or_insert_with(|| ((caller_fid, caller_key.to_vec()), Vec::new()));
        entry.1.push((cid, dispatch));
    };

    // Per-caller-spec dispatch rows (Static for Direct/Cont; Indirect for
    // ClosureCall).
    for ((caller_fid, caller_key), ft) in &mt.specs {
        for (cid, target) in ft.dispatches.iter() {
            let key_ty: Vec<crate::types::Ty> = target.1.clone();
            let dispatch = match cid.slot {
                EmitSlot::ClosureCall => Dispatch::Indirect(target.0, key_ty),
                _ => Dispatch::Static(target.0, key_ty),
            };
            let sort_key = render_ty_key(&mut t, caller_key);
            push_row(
                &mut rows_by_spec,
                *caller_fid,
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
    let any_key_for = |fid: FnId| -> Option<SpecKey> {
        mt.specs
            .keys()
            .find(|(f, k)| *f == fid && k.iter().all(|key| key == &any))
            .cloned()
    };
    for (cid, result) in &reducer_log.consumed {
        let Some(key) = any_key_for(cid.caller) else {
            continue;
        };
        let sort_key = render_ty_key(&mut t, &key.1);
        push_row(
            &mut rows_by_spec,
            cid.caller,
            &key.1,
            cid.clone(),
            Dispatch::Folded(result.clone()),
            sort_key,
        );
    }
    // Reducer Stalled rows — only when no typer-spec dispatched the cid.
    for (cid, reason) in &reducer_log.stalled {
        if spec_cids.contains(cid) {
            continue;
        }
        let Some(key) = any_key_for(cid.caller) else {
            continue;
        };
        let sort_key = render_ty_key(&mut t, &key.1);
        push_row(
            &mut rows_by_spec,
            cid.caller,
            &key.1,
            cid.clone(),
            Dispatch::Stalled(*reason),
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
                    render_dispatch(&mut t, &fn_name, &a.1)
                        .cmp(&render_dispatch(&mut t, &fn_name, &b.1))
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
        mt.specs.keys().map(|(fid, _)| *fid).collect();
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
    type SectionRef<'a> = (SortKey, &'a SpecKey, &'a Vec<(CallsiteId, Dispatch)>);
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
    for (_, (caller_fid, caller_key), rows) in sections {
        let Some(f) = module.fns.iter().find(|f| f.id == *caller_fid) else {
            continue;
        };
        if !should_show(f) {
            continue;
        }
        // fz-try.11 — section header carries the caller spec inline.
        out.push_str(&format!(
            "\n{}{}:\n",
            f.name,
            render_ty_key(&mut t, caller_key)
        ));
        for (cid, dispatch) in rows {
            out.push_str(&format!(
                "  @{} {} -> {}\n",
                render_span(cid.ident.span()),
                slot_str(cid.slot),
                render_dispatch(&mut t, &fn_name, dispatch),
            ));
        }
    }
    out
}

fn compile_pipeline(src: String, source_name: String) -> Compiled {
    let mut t = types::ConcreteTypes;
    let frontend =
        frontend::compile_source_with_types(&mut t, src, source_name).unwrap_or_else(|err| {
            diag::report_or_exit(err.diagnostics.as_slice(), &err.sm);
            std::process::exit(1);
        });
    diag::report_or_exit(frontend.diagnostics.as_slice(), &frontend.sm);
    let main_fn = frontend.module.fn_by_name("main").map(|f| f.id);
    let cm = ir_codegen::compile(&mut t, &frontend.module).unwrap_or_else(|e| {
        diag::render_one_to_stderr(&frontend.sm, &e.to_diagnostic());
        std::process::exit(1);
    });
    // fz-d5b — gate on errors from the typer-side diagnostics
    // (TYPE_OPAQUE_VISIBILITY, TYPE_OPAQUE_ARITHMETIC,
    // TYPE_IMPURE_RECEIVE_GUARD). Severity::Warning entries print and
    // we continue; Severity::Error halts.
    diag::report_or_exit(cm.diagnostics().as_slice(), &frontend.sm);
    Compiled {
        cm,
        main_fn,
        sm: frontend.sm,
        module: frontend.module,
    }
}

/// `fz run <path>` (and the no-argument stdin route) — compile, then drive
/// the program through the Runtime so concurrency-using fixtures work
/// end-to-end.
fn run_jit_src(src: String, source_name: String) {
    let compiled = compile_pipeline(src, source_name);
    let Some(main_fn) = compiled.main_fn else {
        let sm = diag::SourceMap::new();
        let d = diag::Diagnostic::error(
            diag::codes::LOWER_UNBOUND,
            "no `main/0` fn found",
            diag::Span::DUMMY,
        );
        diag::render_one_to_stderr(&sm, &d);
        std::process::exit(1);
    };
    // fz-swt.10 — attach the IR Module so `fz_make_resource` (callable
    // from JIT'd code) can resolve dtor closures.
    let mut rt = runtime::Runtime::new(&compiled.cm, 1).with_module(&compiled.module);
    let _main_pid = rt.spawn(main_fn);
    rt.run_until_idle();
}

#[allow(dead_code)]
fn _force_use() {
    let _ = ast::BinOp::Add;
}
