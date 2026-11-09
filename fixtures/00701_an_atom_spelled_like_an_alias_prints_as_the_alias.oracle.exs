defmodule Oracle do
  def run() do
    IO.inspect(:"Elixir.Foo")
    IO.inspect(:"Elixir.Foo_9.Bar")
    IO.inspect(:"Elixir.F")
    IO.inspect(:Elixir)
    IO.inspect(:Foo)
    IO.inspect(String.to_atom("Elixir.Made.At.Runtime"))
  end
end

Oracle.run()
