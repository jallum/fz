defmodule Pt do
  defstruct [:x, :y]
end

defmodule Qt do
  defstruct [:x, :y]
end

defmodule Yx do
  defstruct [:y, :x]
end

defmodule Oracle do
  def same?(a, b), do: a == b

  def pinned(a, b) do
    case b do
      ^a -> :same
      _ -> :different
    end
  end

  def run do
    p = %Pt{x: 1, y: 2}
    spelled = Map.put(%{x: 1, y: 2}, :__struct__, Pt)
    grown = Map.put(p, :z, 3)
    shrunk = Map.delete(grown, :z)
    fewer = Map.delete(p, :y)
    plain = %{x: 1, y: 2}
    q = %Qt{x: 1, y: 2}

    IO.inspect(p == spelled)
    IO.inspect(spelled == p)
    IO.inspect(p === spelled)
    IO.inspect(p == shrunk)
    IO.inspect(p != spelled)
    IO.inspect(p == grown)
    IO.inspect(same?(p, plain))
    IO.inspect(same?(p, q))
    IO.inspect({p, [spelled]} == {shrunk, [p]})

    IO.inspect(spelled)
    IO.inspect(shrunk)
    IO.inspect({p, [spelled]})
    IO.inspect(Map.delete(fewer, :x))
    IO.inspect(Map.put(%{}, :__struct__, Nowhere))
    IO.inspect(Enum.sort(Map.keys(grown)))
    IO.inspect(String.starts_with?(inspect(grown), "%{"))
    IO.inspect(String.starts_with?(inspect(fewer), "%{"))

    IO.inspect(p < grown)
    IO.inspect(grown < p)
    IO.inspect(spelled < %Pt{x: 1, y: 3})
    IO.inspect(%Pt{x: 1, y: 3} < spelled)
    IO.inspect(p < q)
    IO.inspect(%Qt{x: 0, y: 0} < spelled)
    IO.inspect(plain < p)
    IO.inspect(fewer < plain)
    IO.inspect({9, 9, 9, 9, 9} < p)
    IO.inspect(%Yx{y: 0, x: 2} < %Yx{y: 1, x: 1})
    IO.inspect(Enum.sort([q, spelled, plain, p, grown, fewer]) == [fewer, plain, p, p, q, grown])

    by_point = %{p => :found}
    IO.inspect(Map.get(by_point, spelled))
    IO.inspect(Map.get(by_point, shrunk))
    IO.inspect(Map.get(by_point, grown))
    IO.inspect(map_size(Map.put(by_point, spelled, :again)))
    IO.inspect(length(Enum.uniq([p, spelled, shrunk, grown])))
    IO.inspect(MapSet.size(MapSet.new([p, spelled, shrunk])))
    IO.inspect(spelled in [q, p])
    IO.inspect(pinned(p, spelled))
    IO.inspect(pinned(p, grown))
  end
end

Oracle.run()
