defmodule Oracle do
  def never(), do: Nope.Never

  def run() do
    IO.inspect(never())
    IO.inspect(Atom.to_string(Nope.Never))
  end
end

Oracle.run()
