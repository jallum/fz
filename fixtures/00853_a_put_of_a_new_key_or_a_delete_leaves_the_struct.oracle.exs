defmodule Pt do
  defstruct [:x, :y]
end

defmodule Oracle do
  def run do
    p = %Pt{x: 1, y: 2}
    grown = Map.put(p, :z, 0)
    IO.inspect(Enum.sort(Map.keys(grown)))
    IO.inspect(grown.__struct__)
    IO.inspect(grown.z)
    shrunk = Map.delete(p, :x)
    IO.inspect(Enum.sort(Map.keys(shrunk)))
    IO.inspect(shrunk.__struct__)
    IO.inspect(shrunk.y)
    IO.inspect(Map.delete(p, :__struct__))
    IO.inspect(Map.delete(p, :w))
    IO.inspect(Map.get(p, :x))
  end
end

Oracle.run()
