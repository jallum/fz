defmodule Pt do
  defstruct [:x, :y]
end

defmodule Oracle do
  def bump(v), do: %{v | x: 10}

  def run do
    p = %Pt{x: 1, y: 2}
    IO.inspect(%{p | x: 9})
    IO.inspect(%{p | x: 9, y: 8})
    IO.inspect(bump(p))
    IO.inspect(Map.put(p, :y, 7))
    IO.inspect(%{p | x: 9}.__struct__)
    IO.inspect(p)
    m = %{b: 2}
    IO.inspect(%{m | b: 3})
  end
end

Oracle.run()
