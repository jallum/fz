defmodule Main do
  @spec name(atom()) :: String.t()
  def name(module), do: Atom.to_string(module)

  @spec shout(String.t()) :: String.t()
  def shout(text), do: text <> "!"

  def main() do
    IO.inspect(name(Foo.Bar))
    IO.inspect(shout("hello"))
    IO.inspect(shout(name(Baz)))
  end
end

Main.main()
