mod ast;
mod bitstr;
mod codegen;
mod eval;
mod lexer;
mod parser;
mod typer;
mod types;
mod value;

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
    let (src, show_ast) = parse_args();

    let toks = match Lexer::new(&src).tokenize() {
        Ok(t) => t,
        Err(e) => { eprintln!("{}", e); std::process::exit(1); }
    };

    let prog = match Parser::new(toks).parse_program() {
        Ok(p) => p,
        Err(e) => { eprintln!("{}", e); std::process::exit(1); }
    };

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

fn parse_args() -> (String, bool) {
    let mut show_ast = false;
    let mut path: Option<String> = None;
    for a in std::env::args().skip(1) {
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
