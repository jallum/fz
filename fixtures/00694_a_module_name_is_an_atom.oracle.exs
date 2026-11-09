defmodule Oracle do
  def run() do
    IO.inspect(RuntimeError)
    IO.inspect(Atom.to_string(RuntimeError))
    IO.inspect(RuntimeError == :"Elixir.RuntimeError")
    IO.inspect(is_atom(RuntimeError))
  end
end

Oracle.run()
