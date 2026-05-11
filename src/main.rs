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

/// Drive a source string through the full JIT pipeline (lex → parse →
/// resolve → expand macros → ir_lower → ir_codegen → run main). Used by
/// both `fz run <path>` and the no-argument stdin route.
///
/// Single render path: every error from every stage goes through
/// diag::render_to_stderr. Lex / parse errors carry proper spans; later-
/// stage errors carry the spans threaded in by fz-ul4.20 / .21.
fn run_jit_src(src: String, source_name: String) {
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
    let main_fn = match module.fn_by_name("main") {
        Some(f) => f.id,
        None => {
            let d = diag::Diagnostic::error(
                diag::codes::LOWER_UNBOUND,
                "no `main/0` fn found",
                diag::Span::DUMMY,
            );
            diag::render_one_to_stderr(&sm, &d);
            std::process::exit(1);
        }
    };
    let cm = ir_codegen::compile(&module).unwrap_or_else(|e| {
        diag::render_one_to_stderr(&sm, &e.to_diagnostic());
        std::process::exit(1);
    });
    diag::render_to_stderr(&sm, cm.warnings());
    // Drive through the Runtime (fz-ul4.19.1) so concurrency-using
    // programs work end-to-end. For a program that doesn't call
    // spawn/send/receive this is functionally identical to the simpler
    // `cm.run(main_fn)` path. For concurrent programs it's required —
    // direct cm.run leaves CURRENT_RUNTIME null and any spawn() call
    // would panic.
    let mut rt = runtime::Runtime::new(&cm, 1);
    let _main_pid = rt.spawn(main_fn);
    rt.run_until_idle();
}

#[allow(dead_code)]
fn _force_use() {
    let _ = ast::BinOp::Add;
}
