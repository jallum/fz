mod ast;
mod ast_value;
mod bitstr;
mod diag;
mod eval;
mod fz_ir;
mod fz_value;
mod heap;
mod ir_codegen;
mod ir_interp;
mod ir_runtime;
// ir_liveness removed (fz-ul4.11.31 subsumes .11.30): frame schemas are
// uniformly `[cont_ptr, ...entry_params]` with every Var slot FzValue;
// Cranelift handles temporary spills. The richer per-call liveness was
// never wired into codegen and the .11.31 root walker reads the existing
// schema directly. See fz-ul4.11.30 (subsumed).
mod ir_lower;
mod ir_typer;
mod lexer;
mod macros;
mod parser;
mod process;
mod repl;
mod resolve;
mod runtime;
mod test_runner;
mod typer;
mod types;
mod value;
use parser::Parser;
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

fn run_build(_args: &[String]) {
    eprintln!("fz build: AOT path not yet implemented (tracked by fz-ul4.23.6).");
    std::process::exit(2);
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
    let path = args.first().cloned().unwrap_or_else(|| {
        eprintln!("fz interp <src.fz>");
        std::process::exit(2);
    });
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("read {}: {}", path, e);
        std::process::exit(1);
    });
    let mut sm = diag::SourceMap::new();
    let file_id = sm.add_file(path.clone(), src.clone());
    let toks = lexer::Lexer::with_file(&src, file_id)
        .tokenize()
        .unwrap_or_else(|e| {
            diag::render_one_to_stderr(&sm, &e.to_diagnostic());
            std::process::exit(1);
        });
    let prog = Parser::new(toks).parse_program().unwrap_or_else(|e| {
        diag::render_one_to_stderr(&sm, &e.to_diagnostic());
        std::process::exit(1);
    });
    let mut prog = resolve::flatten_modules(prog).unwrap_or_else(|e| {
        diag::render_one_to_stderr(&sm, &e.to_diagnostic());
        std::process::exit(1);
    });
    if let Err(e) = macros::expand_program(&mut prog) {
        diag::render_one_to_stderr(&sm, &e.to_diagnostic());
        std::process::exit(1);
    }
    let module = ir_lower::lower_program(&prog).unwrap_or_else(|e| {
        diag::render_one_to_stderr(&sm, &e.to_diagnostic());
        std::process::exit(1);
    });
    match ir_interp::run_main(&module) {
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

/// `fz dump <src.fz> [--emit clif] [--fn <name>]` — drive a source file
/// through the full JIT pipeline up to (but not including) finalization,
/// capture the per-fn Cranelift IR text, and print it to stdout. The
/// program is NOT executed.
///
/// Feedback-loop tooling per fz-ul4.23.3. Source-loc interleaving and
/// `--emit asm` are tracked separately (fz-ul4.27, fz-ul4.28).
fn run_dump(args: &[String]) {
    let mut path: Option<String> = None;
    let mut fn_filter: Option<String> = None;
    let mut emit = "clif".to_string();
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
            a if !a.starts_with("--") && path.is_none() => path = Some(a.to_string()),
            a => {
                eprintln!("fz dump: unknown arg `{}`", a);
                std::process::exit(2);
            }
        }
        i += 1;
    }
    let path = path.unwrap_or_else(|| {
        eprintln!("fz dump <src.fz> [--emit clif] [--fn <name>]");
        std::process::exit(2);
    });
    if emit != "clif" {
        eprintln!(
            "fz dump: --emit `{}` not supported yet \
             (only `clif` today; `asm` tracked by fz-ul4.28)",
            emit
        );
        std::process::exit(2);
    }
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("read {}: {}", path, e);
        std::process::exit(1);
    });

    ir_codegen::ir_text_record_enable();
    let _compiled = compile_pipeline(src, path.clone());
    let entries = ir_codegen::ir_text_record_take();

    let mut printed = 0usize;
    for (name, text) in &entries {
        if let Some(filter) = &fn_filter {
            if name != filter {
                continue;
            }
        }
        println!("; fn {}", name);
        println!("{}", text);
        printed += 1;
    }
    if let Some(filter) = &fn_filter {
        if printed == 0 {
            eprintln!(
                "fz dump: no fn named `{}` (available: {})",
                filter,
                entries.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>().join(", ")
            );
            std::process::exit(1);
        }
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
}

fn compile_pipeline(src: String, source_name: String) -> Compiled {
    let mut sm = diag::SourceMap::new();
    let file_id = sm.add_file(source_name, src.clone());

    let toks = lexer::Lexer::with_file(&src, file_id).tokenize().unwrap_or_else(|e| {
        diag::render_one_to_stderr(&sm, &e.to_diagnostic());
        std::process::exit(1);
    });
    let prog = Parser::new(toks).parse_program().unwrap_or_else(|e| {
        diag::render_one_to_stderr(&sm, &e.to_diagnostic());
        std::process::exit(1);
    });
    let mut prog = resolve::flatten_modules(prog).unwrap_or_else(|e| {
        diag::render_one_to_stderr(&sm, &e.to_diagnostic());
        std::process::exit(1);
    });
    if let Err(e) = macros::expand_program(&mut prog) {
        diag::render_one_to_stderr(&sm, &e.to_diagnostic());
        std::process::exit(1);
    }
    let module = ir_lower::lower_program(&prog).unwrap_or_else(|e| {
        diag::render_one_to_stderr(&sm, &e.to_diagnostic());
        std::process::exit(1);
    });
    let main_fn = module.fn_by_name("main").map(|f| f.id);
    let cm = ir_codegen::compile(&module).unwrap_or_else(|e| {
        diag::render_one_to_stderr(&sm, &e.to_diagnostic());
        std::process::exit(1);
    });
    diag::render_to_stderr(&sm, cm.warnings());
    Compiled { cm, main_fn }
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
    let mut rt = runtime::Runtime::new(&compiled.cm, 1);
    let _main_pid = rt.spawn(main_fn);
    rt.run_until_idle();
}

#[allow(dead_code)]
fn _force_use() {
    let _ = ast::BinOp::Add;
}
