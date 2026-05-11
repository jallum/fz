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
mod ir_liveness;
mod ir_lower;
mod ir_typer;
mod lexer;
mod macros;
mod parser;
mod repl;
mod resolve;
mod test_runner;
mod typer;
mod types;
mod value;
// fz-ul4.11.9 cutover: legacy direct-style codegen modules retired. The
// source files (codegen.rs / jit.rs / aot.rs / test_support.rs) are
// preserved verbatim with a top-level `#![cfg(any())]` so test intent can
// be re-verified once ir_codegen reaches feature parity in .11.10-.11.14.

use eval::Interp;
use lexer::Lexer;
use parser::Parser;

const SAMPLE: &str = r#"
fn fact(0), do: 1
fn fact(n) when n > 0, do: n * fact(n - 1)

fn fib(0), do: 0
fn fib(1), do: 1
fn fib(n), do: fib(n - 1) + fib(n - 2)

fn classify(0), do: :zero
fn classify(n) when n > 0, do: :positive
fn classify(_), do: :negative

fn sum([]), do: 0
fn sum([h | t]), do: h + sum(t)

fn map(_, []), do: []
fn map(f, [h | t]), do: [f(h) | map(f, t)]

fn double(x), do: x * 2

fn happy() do
  with {:ok, a} <- {:ok, 1},
       {:ok, b} <- {:ok, 2} do
    a + b
  end
end

fn falls_through() do
  with {:ok, a} <- {:error, "boom"},
       {:ok, _} <- {:ok, a} do
    :unreached
  end
end

fn else_handles() do
  with {:ok, _} <- {:error, "boom"} do
    :unreached
  else
    {:error, msg} -> {:handled, msg}
  end
end

fn build_packet() do
  payload = ~b[1, 2, 3, 4]
  <<0xA5::8, 0::4, 1::4, 4::16, payload::binary>>
end

fn parse_packet(<<magic::8, ver::4, kind::4, len::16, payload::binary-size(len), rest::binary>>) do
  {magic, ver, kind, len, payload, rest}
end

fn user_summary(%{name: n, age: a}) do
  {n, a}
end

fn promote(u) do
  %{u | age: u[:age] + 1}
end

fn maps_demo() do
  alice = %{name: "alice", age: 30, city: "NYC"}
  bob = %{:name => "bob", :age => 25}
  print(user_summary(alice))
  print(user_summary(bob))
  print(promote(alice))
  print(alice[:city])
  print(alice[:missing])
  print(map_get(alice, :name))
  print(map_put(alice, :role, :admin))
end

fn main() do
  pkt = build_packet()
  print(pkt)
  print(parse_packet(pkt))
  print(happy())
  print(falls_through())
  print(else_handles())
  print(fact(10))
  print(fib(20))
  print(classify(-5))
  print(classify(0))
  print(classify(7))
  print(sum([1, 2, 3, 4, 5]))
  print(map(double, [10, 20, 30]))
  print([1, 2, 3] |> sum())
  print(~v[1.0, 2.0, 3.0, 4.0])
  print(~v[1, 2, 3] |> vec_map(double))
  print(~b[0xff, 0x00, 0xab])
  print(~bits[1, 0, 1, 1, 0, 0, 1])
  print(vec_reduce(~v[1, 2, 3, 4, 5], 0, fn (a, b) -> a + b))
  print(~v[1, 2, 3, 4, 5] |> vec_reduce(0, fn (a, b) -> a + b))
  maps_demo()
end
"#;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.first().map(String::as_str) == Some("build") {
        run_build(&args[1..]);
        return;
    }
    if args.first().map(String::as_str) == Some("run") {
        run_jit(&args[1..]);
        return;
    }
    if args.first().map(String::as_str) == Some("repl") {
        if let Err(e) = repl::run() {
            eprintln!("repl: {}", e);
            std::process::exit(1);
        }
        return;
    }
    if args.first().map(String::as_str) == Some("test") {
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

    let (src, show_ast) = parse_args(&args);

    let toks = match Lexer::new(&src).tokenize() {
        Ok(t) => t,
        Err(e) => { eprintln!("{}", e); std::process::exit(1); }
    };

    let prog = match Parser::new(toks).parse_program() {
        Ok(p) => p,
        Err(e) => { eprintln!("{}", e); std::process::exit(1); }
    };
    let mut prog = match resolve::flatten_modules(prog) {
        Ok(p) => p,
        Err(e) => { eprintln!("module resolution: {}", e); std::process::exit(1); }
    };
    if let Err(e) = macros::expand_program(&mut prog) {
        eprintln!("macro expansion: {}", e); std::process::exit(1);
    }

    if show_ast {
        for item in &prog.items { println!("{:#?}", item); }
        return;
    }

    let interp = Interp::new();
    if let Err(e) = interp.load_program(&prog) {
        eprintln!("load error: {}", e); std::process::exit(1);
    }
    if let Err(e) = interp.call_named("main", vec![]) {
        eprintln!("runtime error: {}", e); std::process::exit(1);
    }
}

fn run_build(_args: &[String]) {
    eprintln!(
        "fz build: AOT path is being rewired through ir_codegen \
         (fz-ul4.11.9 cutover); reinstated alongside heap-type support \
         in .11.10-.11.14"
    );
    std::process::exit(2);
}

fn run_jit(args: &[String]) {
    // Single render path: every error from every stage goes through
    // diag::render_to_stderr. Lex/parse errors come with proper spans;
    // resolve / macro / lower / codegen errors are wrapped in a DUMMY-
    // span Diagnostic for now (a future ticket carries spans through
    // those stages too — they're rarer than user-visible lex/parse).
    let src_path = args.first().cloned().unwrap_or_else(|| {
        eprintln!("fz run <src.fz>");
        std::process::exit(2);
    });
    let src = std::fs::read_to_string(&src_path).unwrap_or_else(|e| {
        eprintln!("read {}: {}", src_path, e);
        std::process::exit(1);
    });

    let mut sm = diag::SourceMap::new();
    let file_id = sm.add_file(src_path.clone(), src.clone());

    let toks = lexer::Lexer::with_file(&src, file_id).tokenize().unwrap_or_else(|e| {
        diag::render_one_to_stderr(&sm, &e.to_diagnostic());
        std::process::exit(1);
    });
    let prog = Parser::new(toks).parse_program().unwrap_or_else(|e| {
        diag::render_one_to_stderr(&sm, &e.to_diagnostic());
        std::process::exit(1);
    });
    let mut prog = resolve::flatten_modules(prog).unwrap_or_else(|e| {
        let d = diag::Diagnostic::error(diag::codes::RESOLVE_UNKNOWN_MODULE, e, diag::Span::DUMMY);
        diag::render_one_to_stderr(&sm, &d);
        std::process::exit(1);
    });
    if let Err(e) = macros::expand_program(&mut prog) {
        let d = diag::Diagnostic::error(diag::codes::MACRO_BODY_FAILED, e, diag::Span::DUMMY);
        diag::render_one_to_stderr(&sm, &d);
        std::process::exit(1);
    }
    let module = ir_lower::lower_program(&prog).unwrap_or_else(|e| {
        let d = diag::Diagnostic::error(
            diag::codes::LOWER_UNSUPPORTED,
            format!("{}", e),
            diag::Span::DUMMY,
        );
        diag::render_one_to_stderr(&sm, &d);
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
        let d = diag::Diagnostic::error(
            diag::codes::CODEGEN_SCHEMA_MISSING,
            format!("{:?}", e),
            diag::Span::DUMMY,
        );
        diag::render_one_to_stderr(&sm, &d);
        std::process::exit(1);
    });
    // Typer-emitted warnings (unreachable arms, etc.) flow through the
    // same renderer.
    diag::render_to_stderr(&sm, cm.warnings());
    let _ = cm.run(main_fn);
}

fn parse_args(args: &[String]) -> (String, bool) {
    let mut show_ast = false;
    let mut path: Option<String> = None;
    for a in args {
        match a.as_str() {
            "--ast" => show_ast = true,
            other => path = Some(other.to_string()),
        }
    }
    let src = match path {
        Some(p) => std::fs::read_to_string(p).expect("read source"),
        None => SAMPLE.to_string(),
    };
    (src, show_ast)
}

#[allow(dead_code)]
fn _force_use() {
    let _ = ast::BinOp::Add;
}
