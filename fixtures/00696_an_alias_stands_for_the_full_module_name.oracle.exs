defmodule Oracle do
  alias Foo.Bar, as: B
  alias Foo.Baz

  def aliased(), do: B

  def run() do
    IO.inspect(aliased())
    IO.inspect(B == Foo.Bar)
    IO.inspect(Atom.to_string(B))
    IO.inspect(Baz)
    IO.inspect(B.Inner)
  end
end

Oracle.run()
