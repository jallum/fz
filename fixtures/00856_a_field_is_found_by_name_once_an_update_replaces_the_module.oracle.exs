defmodule Near do
  defstruct [:x, :y]
end

defmodule Far do
  defstruct [:y, :x]
end

defmodule Oracle do
  def rename(v, m), do: %{v | __struct__: m}

  def run do
    p = %Near{x: 1, y: 2}
    q = %{p | __struct__: Far}
    IO.inspect(q.x)
    IO.inspect(q.y)
    IO.inspect(q.__struct__)
    r = rename(p, Far)
    IO.inspect(r.x)
    IO.inspect(r.__struct__)
    s = %{p | __struct__: Near, y: 5}
    IO.inspect(s.x)
    IO.inspect(s.y)
    IO.inspect(s.__struct__)
    IO.inspect(p.x)
    IO.inspect(p.__struct__)
  end
end

Oracle.run()
