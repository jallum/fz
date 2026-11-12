defmodule Pt do
  defstruct [:x, :y]
end

defmodule Geo.Pt do
  defstruct [:lat]
end

defmodule Oracle do
  def module_of(v), do: v.__struct__

  def run do
    p = %Pt{x: 1, y: 2}
    IO.inspect(p.__struct__)
    IO.inspect(module_of(p))
    IO.inspect(p.__struct__ == Pt)
    IO.inspect(module_of(p) == Pt)
    IO.inspect(module_of(p) == Geo.Pt)
    g = %Geo.Pt{lat: 1}
    IO.inspect(g.__struct__)
    IO.inspect(module_of(g))
  end
end

Oracle.run()
