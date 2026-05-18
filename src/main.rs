mod ast;
mod ast_value;
mod bitstr;
mod diag;
mod eval;
mod fz_ir;
mod ir_codegen;
mod ir_interp;
// ir_liveness removed (fz-ul4.11.31 subsumes .11.30): frame schemas are
// uniformly `[cont_ptr, ...entry_params]` with every Var slot FzValue;
// Cranelift handles temporary spills. The richer per-call liveness was
// never wired into codegen and the .11.31 root walker reads the existing
// schema directly. See fz-ul4.11.30 (subsumed).
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
mod test_runner;
mod type_expr;
mod typer;
mod types;
mod value;
use parser::Parser;
use std::io::{IsTerminal, Read};

/// fz-ul4.31.6 — Run `@spec` validation against the lowered IR. Prints
/// every diagnostic and exits non-zero if any are errors. Called by
/// the `run` / `jit` / `aot` drivers immediately after `lower_program`
/// so all three paths produce identical accept/reject verdicts.
fn validate_specs_or_exit(prog: &ast::Program, module: &fz_ir::Module, sm: &diag::SourceMap) {
    let mt = ir_typer::type_module(module);
    let mut diags = spec_check::validate_specs(prog, module, &mt);
    // fz-ul4.45 — pattern-match correctness analysis. Unreachable clauses
    // and inexhaustive matches surface as warnings here (non-fatal). The
    // pattern checker is gated to fns that actually survive the reducer:
    // a `:function_clause` halt the warning worries about can only fire
    // from a body that exists at runtime, and a fn that fully dissolves
    // (e.g. ast_eval's `eval`) has no such body. Compute the survivor
    // set on a reduced clone of the module so warnings track what
    // codegen will actually emit.
    let survivors = compute_survivors(module);
    diags.extend(pattern_check::check_program(prog, Some(&survivors)));
    let has_error = diags.iter().any(|d| d.severity == diag::Severity::Error);
    for d in &diags {
        diag::render_one_to_stderr(sm, d);
    }
    if has_error {
        std::process::exit(1);
    }
}

/// Names + arities of user fns whose body survives the reducer — i.e.
/// the typer registers at least one spec for them on a reduced module.
/// Used by `validate_specs_or_exit` to skip pattern_check warnings on
/// fully-dissolved fns.
fn compute_survivors(module: &fz_ir::Module) -> std::collections::HashSet<(String, usize)> {
    let mut reduced = module.clone();
    ir_reducer::reduce_module(&mut reduced);
    let mt = ir_typer::type_module(&reduced);
    let mut out = std::collections::HashSet::new();
    for (fid, _) in mt.specs.keys() {
        if let Some(&idx) = reduced.fn_idx.get(fid) {
            let f = &reduced.fns[idx];
            let arity = f.block(f.entry).params.len();
            out.insert((f.name.clone(), arity));
        }
    }
    out
}

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
fn run_build(args: &[String]) {
    let mut src_path: Option<String> = None;
    let mut out_path: Option<String> = None;
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

    let mut sm = diag::SourceMap::new();
    let file_id = sm.add_file(src_path.clone(), src.clone());
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
    validate_specs_or_exit(&prog, &module, &sm);
    let obj_name = std::path::Path::new(&src_path)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("fz_program");
    let artifact = ir_codegen::compile_aot(&module, obj_name).unwrap_or_else(|e| {
        diag::render_one_to_stderr(&sm, &e.to_diagnostic());
        std::process::exit(1);
    });
    if artifact.main_symbol.is_none() {
        eprintln!("fz build: no `main/0` fn found; nothing to link.");
        std::process::exit(1);
    }
    diag::render_to_stderr(&sm, &artifact.diagnostics);

    // Write the object next to the output, then invoke cc.
    let obj_temp = std::path::PathBuf::from(format!("{}.o", out_path));
    std::fs::write(&obj_temp, &artifact.object).unwrap_or_else(|e| {
        eprintln!("write object {}: {}", obj_temp.display(), e);
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
    let status = cc.status().unwrap_or_else(|e| {
        eprintln!("fz build: failed to invoke cc: {}", e);
        std::process::exit(1);
    });
    if !status.success() {
        eprintln!("fz build: cc exited {}", status);
        std::process::exit(1);
    }
    // Drop the intermediate .o on success.
    let _ = std::fs::remove_file(&obj_temp);
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
    validate_specs_or_exit(&prog, &module, &sm);
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
    let emit_clif = matches!(emit.as_str(), "clif" | "both");
    let emit_asm = matches!(emit.as_str(), "asm" | "both");
    let emit_specs = emit.as_str() == "specs";
    // fz-jg5.8 (RED.7) — user-facing diagnostic: list every emitted body
    // and (in v1) its source spec key. Boundary attribution per-call is a
    // follow-on; this v1 prints the spec set and a single-line summary so
    // the user can see "0 user fns" for fully-reduced programs.
    let emit_bodies = emit.as_str() == "bodies";
    if !emit_clif && !emit_asm && !emit_specs && !emit_bodies {
        eprintln!("fz dump: --emit must be one of `clif`, `asm`, `both`, `specs`, `bodies`");
        std::process::exit(2);
    }
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("read {}: {}", path, e);
        std::process::exit(1);
    });

    if emit_specs {
        if fn_filter.is_some() {
            eprintln!("fz dump: --fn is ignored with --emit specs (spec dump is per-module)");
        }
        let dump = dump_specs_pipeline(src, path.clone());
        print!("{}", dump);
        return;
    }

    if emit_bodies {
        if fn_filter.is_some() {
            eprintln!("fz dump: --fn is ignored with --emit bodies");
        }
        print!("{}", dump_bodies_pipeline(src, path.clone()));
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
        println!("; fn {}", name);
        if emit_clif && let Some(text) = clif_map.get(name) {
            println!("{}", format_clif(text, &compiled.sm));
        }
        if emit_asm && let Some(text) = asm_map.get(name) {
            if emit_clif {
                println!("; ---- asm ----");
            }
            println!("{}", text);
        }
        printed += 1;
    }
    if let Some(filter) = &fn_filter
        && printed == 0
    {
        eprintln!(
            "fz dump: no fn named `{}` (available: {})",
            filter,
            order.join(", ")
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
}

/// fz-73m — drive a source string through lex → parse → resolve → macros
/// → ir_lower → type_module, then pretty-print `ModuleTypes` for golden
/// inspection. Skips codegen entirely; the dump is a typer-only view.
fn dump_specs_pipeline(src: String, source_name: String) -> String {
    let mut sm = diag::SourceMap::new();
    let file_id = sm.add_file(source_name, src.clone());
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
    validate_specs_or_exit(&prog, &module, &sm);
    let mt = ir_typer::type_module(&module);
    ir_typer::pretty_module_types(&module, &mt)
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
    let mut sm = diag::SourceMap::new();
    let file_id = sm.add_file(source_name, src.clone());
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
    let mut module = ir_lower::lower_program(&prog).unwrap_or_else(|e| {
        diag::render_one_to_stderr(&sm, &e.to_diagnostic());
        std::process::exit(1);
    });
    // Run the reducer pass directly so the bodies dump reflects what
    // codegen would see, without going all the way to JIT.
    ir_reducer::reduce_module(&mut module);
    let mt: ModuleTypes = ir_typer::type_module(&module);

    // Group surviving specs by user-fn name. Skip the conventional
    // synthetic helpers (k_*, fn_clause_*, lambda_*) — they're
    // continuations or pattern-clause bodies, not user fns.
    let mut by_name: std::collections::BTreeMap<String, Vec<&Vec<crate::types::Descr>>> =
        std::collections::BTreeMap::new();
    for ((fid, key), _) in &mt.specs {
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
            let parts: Vec<String> = key.iter().map(|d| format!("{}", d)).collect();
            out.push_str(&format!("    [{}]\n", parts.join(", ")));
        }
    }
    out
}

fn compile_pipeline(src: String, source_name: String) -> Compiled {
    let mut sm = diag::SourceMap::new();
    let file_id = sm.add_file(source_name, src.clone());

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
    validate_specs_or_exit(&prog, &module, &sm);
    let main_fn = module.fn_by_name("main").map(|f| f.id);
    let cm = ir_codegen::compile(&module).unwrap_or_else(|e| {
        diag::render_one_to_stderr(&sm, &e.to_diagnostic());
        std::process::exit(1);
    });
    diag::render_to_stderr(&sm, cm.warnings());
    Compiled { cm, main_fn, sm }
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
