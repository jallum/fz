defmodule Oracle do
  def run() do
    IO.inspect(Foo.Bar)
    IO.inspect(Atom.to_string(Foo.Bar.Baz))
    IO.inspect(Foo.Bar == :"Elixir.Foo.Bar")
    IO.inspect(Foo.Bar == Foo)
  end
end

Oracle.run()
