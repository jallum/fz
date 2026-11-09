defmodule Names do
  @spec name(atom()) :: String.t()
  def name(module), do: Atom.to_string(module)

  def kind(value) when is_atom(value), do: :atom
  def kind(_value), do: :other

  def is_bar(value) when value == Foo.Bar, do: true
  def is_bar(_value), do: false
end

defmodule Oracle do
  def run() do
    IO.inspect(Names.name(Foo.Bar))
    IO.inspect(Names.kind(RuntimeError))
    IO.inspect(Names.kind(1))
    IO.inspect(Names.is_bar(Foo.Bar))
    IO.inspect(Names.is_bar(Foo))
  end
end

Oracle.run()
